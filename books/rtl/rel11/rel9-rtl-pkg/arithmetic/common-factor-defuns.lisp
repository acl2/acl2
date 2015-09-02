; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "inverted-factor")

;combine with inverted-factor?

#|

Note.  I'd really like to use multi-sets to handle common factors that appear multiple times (e.g., x in
(+ (* x x) (* a x x)).  But for right now, we only handle one ocurrence of each factor.  (Multiple occurrences
will be handled the next time our rules are tried.

|#

;todo: make these tail-recursive...

(defund my-intersection-equal (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))))
  (cond ((endp x) nil)
	((member-equal (car x) y)
	 (cons (car x) (my-intersection-equal (cdr x) y)))
	(t (my-intersection-equal (cdr x) y))))

(defun adjoin-equal (x l)
  (declare (xargs :guard (true-listp l)))
  (if (member-equal x l)
      l
    (cons x l)))


;remove the first occurrence of x from l, if any...
(defund remove-one (x l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) nil)
        ((equal x (car l)) (cdr l))
        (t (cons (car l) (remove-one x (cdr l))))))

(defthm remove-one-preserves-true-listp
  (implies (true-listp l)
           (true-listp (remove-one x l)))
  :hints (("Goal" :in-theory (enable remove-one))))


;In this book, "ground-term" means any term except those which are calls to binary-+ or binary-*.

;TERM is a product of one or more ground-terms.
;Returns a list of the ground-terms which are multiplied in TERM.  The list will contain no duplicates.
;Assumes TERM is normalized (either a single ground-term or a correctly associated product of ground-terms.)
(defund get-factors-of-product (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (consp term)) ;term was a symbol
      (list term)
    (if (not (equal (car term) 'binary-*))
        (list term) ;must be a ground-term...
      (adjoin-equal (cadr term) (get-factors-of-product (caddr term))))))

(defthm get-factors-of-product-true-listp
  (true-listp (get-factors-of-product term))
  :hints (("Goal" :in-theory (enable get-factors-of-product))))

(in-theory (disable true-listp
                    FACTOR-SYNTAXP
                    PRODUCT-SYNTAXP
                    SUM-OF-PRODUCTS-SYNTAXP))

(defund find-inverted-factors-in-list (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      nil
    (if (and (consp (car lst))
             (equal (caar lst) 'unary-/))
        (cons (car lst) (find-inverted-factors-in-list (cdr lst)))
       (find-inverted-factors-in-list (cdr lst)))))

(defund remove-cancelling-factor-pairs-helper (inverted-factor-lst lst)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp inverted-factor-lst))))
  (if (endp inverted-factor-lst)
      lst
    (let* ((inverted-factor (car inverted-factor-lst))
           (non-inverted-factor (and (consp inverted-factor)
                                     (consp (cdr inverted-factor))
                                     (cadr inverted-factor))))
      (if (member-equal non-inverted-factor lst)
          (remove-cancelling-factor-pairs-helper
           (cdr inverted-factor-lst)
           (remove-one inverted-factor
                       (remove-one non-inverted-factor
                                   lst)))
        (remove-cancelling-factor-pairs-helper (cdr inverted-factor-lst) lst)))))

(defthm remove-cancelling-factor-pairs-helper-preserves-true-listp
  (implies (true-listp l)
           (true-listp (remove-cancelling-factor-pairs-helper i l)))
  :hints (("Goal" :in-theory (enable  remove-cancelling-factor-pairs-helper))))

;removes any pair of elements <term> and (/ <term>) from the list, so that we don't cancel something that will
;get blown away anyway.  Note that this is only an issue if we have unnormalized subterms, which *can* happen.
(defund remove-cancelling-factor-pairs (lst)
  (declare (xargs :guard (true-listp lst)))
  (let* ((inverted-factor-lst (find-inverted-factors-in-list lst)))
    (if inverted-factor-lst
        (remove-cancelling-factor-pairs-helper inverted-factor-lst lst)
      lst)))

(defthm remove-cancelling-factor-pairs-preserves-true-listp
  (implies (true-listp l)
           (true-listp (remove-cancelling-factor-pairs l)))
  :hints (("Goal" :in-theory (enable  remove-cancelling-factor-pairs))))


;TERM should be a "normalized sum of products" - "should" in what sense? BOZO
;returns a list of the factors common to each product in TERM
(defund find-common-factors-in-sum-of-products-aux (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (sum-of-products-syntaxp term))
      nil
    (if (not (consp term)) ;term was a symbol
        (list term)
      (case (car term)
        (binary-+ (my-intersection-equal (get-factors-of-product (cadr term))
                                         (find-common-factors-in-sum-of-products-aux (caddr term))))
        (otherwise (get-factors-of-product term)) ;must be a single product...
        ))))

(defthm find-common-factors-in-sum-of-products-aux-true-listp
  (true-listp (find-common-factors-in-sum-of-products-aux term))
  :hints (("Goal" :in-theory (enable find-common-factors-in-sum-of-products-aux))))

;helps ensure that we don't cancel a factor whose inverse is also a factor (in this case the bad factor won't
;be considered a "common factor" of whichever side also has its inverse among its factors.
(defund find-common-factors-in-sum-of-products (term)
  (declare (xargs :guard (pseudo-termp term)))
  (remove-cancelling-factor-pairs (find-common-factors-in-sum-of-products-aux term)))

(defthm find-common-factors-in-sum-of-products-true-listp
  (true-listp (find-common-factors-in-sum-of-products term))
  :hints (("Goal" :in-theory (enable find-common-factors-in-sum-of-products))))

;(REMOVE-CANCELLING-FACTOR-PAIRS '(a b (unary-/ a) d d d c (unary-/ d) (unary-/ d) (unary-/ d)))

(defund make-product-from-list-of-factors (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      1
    (if (endp (cdr lst))
        (car lst)
      (list 'binary-* (car lst) (make-product-from-list-of-factors (cdr lst))))))

(defun find-common-factors-to-cancel (lhs rhs)
  (declare (xargs :guard (and (pseudo-termp lhs) (pseudo-termp rhs))))
  (remove-cancelling-factor-pairs ; do we need this call?
   (my-intersection-equal
    (find-common-factors-in-sum-of-products lhs)
    (find-common-factors-in-sum-of-products rhs))))

(defund bind-k-to-common-factors (lhs rhs)
  (declare (xargs :guard-hints (("Goal" :use (:instance remove-cancelling-factor-pairs-preserves-true-listp
                                                        (l (MY-INTERSECTION-EQUAL (FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS LHS)
                                                                                  (FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS RHS))))))
                  :guard (and (pseudo-termp lhs) (pseudo-termp rhs))))
  (let* ((common-factor-list (find-common-factors-to-cancel lhs rhs)))
    (if (endp common-factor-list)
        nil
      (list (cons 'k (make-product-from-list-of-factors common-factor-list))))))

