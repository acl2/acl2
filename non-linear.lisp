; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

;=================================================================

; We here begin the support functions for non-linear arithmetic.

;=================================================================

(defun cleanse-type-alist (type-alist pt)

; This function removes equality facts from the type-alist in
; preparation for the call to rewrite-linear-term-lst in
; add-terms-and-lemmas.

; In order to see why we need this function now, redefine
; cleanse-type-alist to be the identity and trace
; rewrite-linear-term-lst and linearize in the (failed) proof
; of the following lemma:

; (defthm uniqueness-of-+-inverses-lemma
;     (implies (and (acl2-numberp x)
;                   (acl2-numberp y)
;                   (equal (+ x y)
;                          0))
;              (equal (- x) y))
;   :rule-classes nil)

  (cond ((null type-alist)
         nil)
        ((to-be-ignoredp (cddar type-alist) pt)
         (cleanse-type-alist (cdr type-alist) pt))
        (t
         (cons (car type-alist)
               (cleanse-type-alist (cdr type-alist) pt)))))

(defun var-with-divisionp (var)

; We test whether  var is of the form
; 1. (/ x) or (expt (/ x) n), or    [don't change this line without
; 2. (expt x c) or (expt x (* c y))  seeing the Warning below]
; where c is a negative constant.

; Warning:  If you change this code, search for other instances of
; ``1. (/ x) or (expt (/ x) n)'' and adjust those comments
; appropriately.

; Warning: Keep this function in sync with invert-var.

  (cond ((eq (fn-symb var) 'EXPT)
         (let ((base (fargn var 1))
               (exponent (fargn var 2)))
           (or (and (eq (fn-symb base) 'UNARY-/)
                    (not (eq (fn-symb (fargn base 1)) 'BINARY-+)))
               (and (not (eq (fn-symb base) 'BINARY-+))
                    (quotep exponent)
                    (integerp (unquote exponent))
                    (< (unquote exponent) 0))
               (and (not (eq (fn-symb base) 'BINARY-+))
                    (eq (fn-symb exponent) 'BINARY-*)
                    (quotep (fargn exponent 1))
                    (integerp (unquote (fargn exponent 1)))
                    (< (unquote (fargn exponent 1)) 0)))))
        (t
         (and (eq (fn-symb var) 'UNARY-/)
              (not (eq (fn-symb (fargn var 1)) 'BINARY-+))))))

(defun varify (x)

; We ensure that x is a legitimate pot-label.  See invert-var from whence
; this is called.

  (cond ((quotep x)
         (er hard 'varify
             "This should not have happened.  The supposed ~
              variable, ~x0, is instead a constant."
             x))
        ((equal (fn-symb x) 'BINARY-+)

;;; We have to pick one.

         (if (quotep (fargn x 1))
             (varify (fargn x 2))
           (varify (fargn x 1))))
        ((and (equal (fn-symb x) 'BINARY-*)
              (quotep (fargn x 1)))
         (varify (fargn x 2)))
        (t
         x)))

(defun varify! (x)
  (let ((temp (varify x)))
    (if (good-pot-varp temp)
        temp
      (er hard 'varify!
          "Varify! is supposed to return a good-pot-varp, but ~
           returned ~x0 on ~x1."
          temp x))))

(defun varify!-lst1 (lst acc)
  (if (null lst)
      acc
    (varify!-lst1 (cdr lst) (cons (varify! (car lst)) acc))))

(defun varify!-lst (lst)

; This is used in expanded-new-vars-in-pot-lst, and we want to
; reverse the list.  Thus the use of an accumulator.

  (varify!-lst1 lst nil))

(defun invert-var (var)

; Var is an arithmetic ACL2 term.  We return a term suitable for use
; as an unknown in a poly, but that's all we guarantee.  The idea is
; that the term is ``relevant'' to the non-linear properties of var
; and we try to return the multiplicative inverse.  We expect to go
; find additional polys about this term.

  (cond ((eq (fn-symb var) 'EXPT)
         (let ((base (fargn var 1))
               (exponent (fargn var 2)))
           (cond ((eql exponent ''-1)
                  (varify! base))
                 ((eq (fn-symb base) 'UNARY-/)
                  (fcons-term* 'EXPT (fargn base 1) exponent))
                 ((eq (fn-symb exponent) 'UNARY--)
                  (fcons-term* 'EXPT base (fargn exponent 1)))
                 ((and (quotep exponent)
                       (integerp (unquote exponent))
                       (< (unquote exponent) 0))
                  (fcons-term* 'EXPT base (kwote (- (unquote exponent)))))
                 ((and (eq (fn-symb exponent) 'BINARY-*)
                       (quotep (fargn exponent 1))
                       (integerp (unquote (fargn exponent 1)))
                       (< (unquote (fargn exponent 1)) 0))
                  (fcons-term* 'EXPT
                               base
                               (cons-term
                                'BINARY-*
                                (list
                                 (kwote (- (unquote (fargn exponent 1))))
                                 (fargn exponent 2)))))
                 (t
                  (fcons-term* 'EXPT
                               (cons-term 'UNARY-/ (list base))
                               exponent)))))
        ((eq (fn-symb var) 'UNARY-/)
         (varify! (fargn var 1)))
        (t
         (cons-term 'UNARY-/ (list var)))))

(defun part-of1 (var1 var2)

; NOTE: Note that we are implicitly assuming that var2 is right
; associated.  This should be taken care of some day.  Perhaps what I
; should do is take the fringe of both vars, and do a simple set
; difference.

  (cond ((or (variablep var2)
             (fquotep var2))
         (if (equal var1 var2)
             *1*
             nil))
        ((eq (ffn-symb var2) 'BINARY-*)
         (let ((arg1 (fargn var2 1))
               (arg2 (fargn var2 2)))
           (if (equal var1 arg1)
               arg2
               (let ((new-var2 (part-of1 var1 arg2)))
                 (cond ((null new-var2)
                        nil)
                       ((equal new-var2 ''1)
                        arg1)
                       (t
                        (cons-term 'BINARY-*
                                  (list arg1
                                        new-var2))))))))
        (t
         (if (equal var1 var2)
             *1*
             nil))))

(defun part-of (var1 var2)

; We ask whether the factors of var1 are a subset of the factors of
; var2.  If so, we return a naive calculation of (/ var2 var1).

  (cond ((or (variablep var1)
             (fquotep var1))
         (part-of1 var1 var2))
        ((eq (ffn-symb var1) 'BINARY-*)
         (let ((new-var2 (part-of (fargn var1 1) var2)))
           (cond (new-var2
                  (part-of (fargn var1 2) new-var2))
                 (t
                  nil))))
        (t
         (part-of1 var1 var2))))

(defun product-already-triedp (var-list products-already-tried)

; Var-list is a list of ACL2 terms, products-already-tried is a
; list of lists of ACL2 terms.  If (a permutation of) var-list
; appears in products-already-tried, we return t.  Otherwise, we
; return nil.

  (cond ((null products-already-tried)
         nil)
        (t
         (or (equal var-list (car products-already-tried))
             (product-already-triedp var-list
                                     (cdr products-already-tried))))))

(defun too-many-polysp (var-lst pot-lst counter)

; Var-list is a list of pot-labels from pot-lst, and counter is initially
; 1.  We we are about to multiply the polys from the pots in var-lst,
; we first check whether doing so would generate too many polys.

; Note: This function has a magic number, 20, which probably should be
; settable.

  (cond
   ((null var-lst)
    (< 20 counter))
   (t
    (too-many-polysp (cdr var-lst)
                      pot-lst
                      (* counter
                         (length (polys-with-var1 (car var-lst) pot-lst)))))))

(defun expanded-new-vars-in-pot-lst2 (new-var vars-to-skip vars-to-return)

; We explore the term new-var and accumulate into vars-to-skip and
; vars-to-return all the tips of the BINARY-* tree and the inverses of
; vars with division.

  (cond
   ((or (member-equal new-var vars-to-skip)
        (quotep new-var)
        (eq (fn-symb new-var) 'BINARY-+))
    (mv vars-to-skip vars-to-return))
   ((eq (fn-symb new-var) 'BINARY-*)
    (let ((new-factor (fargn new-var 1)))
      (if (or (member-equal new-factor vars-to-skip)
              (quotep new-factor)
              (eq (fn-symb new-factor) 'BINARY-+))
          (expanded-new-vars-in-pot-lst2 (fargn new-var 2)
                                         vars-to-skip
                                         vars-to-return)
        (expanded-new-vars-in-pot-lst2 (fargn new-var 2)
                                       (cons new-factor vars-to-skip)
                                       (cons new-factor vars-to-return)))))
   ((var-with-divisionp new-var)
    (let ((inverted-var (invert-var new-var)))
      (if (member-equal inverted-var vars-to-skip)
          (mv (cons new-var vars-to-skip)
              (cons new-var vars-to-return))
        (mv (cons new-var (cons inverted-var vars-to-skip))
            (cons new-var (cons inverted-var vars-to-return))))))
   (t
    (mv (cons new-var vars-to-skip)
        (cons new-var vars-to-return)))))

(defun expanded-new-vars-in-pot-lst1 (new-pot-lst vars-to-skip
                                                  vars-to-return)

; We explore all the terms in new-pot-lst and collect all the ``new''
; vars (relative to vars-to-skip) and the inverses of the vars with
; division.  We also collect all the factors of the vars we collect
; above, and their inverses.  We accumulate onto both vars-to-skip and
; vars-to-return, but only return the latter.

  (if (null new-pot-lst)
      vars-to-return
    (let ((new-var (access linear-pot (car new-pot-lst) :var)))
      (cond
       ((member-equal new-var vars-to-skip)
        (expanded-new-vars-in-pot-lst1 (cdr new-pot-lst)
                                       vars-to-skip
                                       vars-to-return))
       ((var-with-divisionp new-var)
        (let* ((inverse-var (invert-var new-var))

; We keep vars-to-skip a superset of vars-to-return.

               (new-vars-to-skip (if (member-equal inverse-var vars-to-skip)
                                     (cons new-var vars-to-skip)
                                   (cons new-var (cons inverse-var
                                                       vars-to-skip))))
               (new-vars-to-return (if (member-equal inverse-var vars-to-skip)
                                       (cons new-var vars-to-return)
                                     (cons new-var (cons inverse-var
                                                         vars-to-return)))))
           (expanded-new-vars-in-pot-lst1 (cdr new-pot-lst)
                                          new-vars-to-skip
                                          new-vars-to-return)))
       ((eq (fn-symb new-var) 'BINARY-*)
        (mv-let (new-vars-to-skip new-vars-to-return)
          (expanded-new-vars-in-pot-lst2 new-var
                                         vars-to-skip
                                         vars-to-return)
          (expanded-new-vars-in-pot-lst1 (cdr new-pot-lst)
                                         (cons new-var new-vars-to-skip)
                                         (cons new-var new-vars-to-return))))
       (t
        (expanded-new-vars-in-pot-lst1 (cdr new-pot-lst)
                                       (cons new-var vars-to-skip)
                                       (cons new-var vars-to-return)))))))

(defun expanded-new-vars-in-pot-lst (new-pot-lst old-pot-lst)

; This is a variant of new-vars-in-pot-lst.  See the comments there.
; Here, if a new var is a product, we recursively add all its individual
; factors to the list of new vars as well as the product itself.
; E. g., if a new var is (* x (foo y) (bar z)), we add
; x, (foo y), (bar z), and (* x (foo y) (bar z)) to the new var list.
; In addition, if a var or one of its factors is of the form
; 1. (/ x) or (expt (/ x) n) or
; 2. (expt x c) or (expt x (* c y)), where c is a negative integer,
; we expand the multiplicative inverse.

; We need to generate a list of vars to skip.  We expand the vars in
; old-pot-lst.

  (let ((vars-to-skip (expanded-new-vars-in-pot-lst1
                       old-pot-lst
                       nil ; vars-to-skip
                       nil)))
    (varify!-lst
     (expanded-new-vars-in-pot-lst1 new-pot-lst
                                    vars-to-skip
                                    nil))))

(defun extract-bounds (bounds-polys)

; Bounds-polys is a list of bounds-polys as returned by bounds-polys-with-var.
; It is either nil meaning no bounds were found, a list of one element
; which is either an upper or lower bound poly, or a list of length two
; consisting of an upper and lower bound poly.  We return six items ---
; any of which may be nil if it was not found --- the lower bound, its
; relation, its ttree, an upper bound, its relation, and its ttree.

  (cond ((null bounds-polys)
         (mv nil nil nil nil nil nil))
        ((null (cdr bounds-polys))
         ;; We have only a lower, or upper bound.
         (if (< (first-coefficient (car bounds-polys)) 0)
             ;; ((var < c)), we have only an upper bound.
             (mv nil nil nil
                 (access poly (car bounds-polys) :constant)
                 (access poly (car bounds-polys) :relation)
                 (access poly (car bounds-polys) :ttree))
           ;; ((c < var)), we have only a lower bound.
           (mv (- (access poly (car bounds-polys) :constant))
               (access poly (car bounds-polys) :relation)
               (access poly (car bounds-polys) :ttree)
               nil nil nil)))
        (t
         ;; We have both a lower and upper bound.
         (if (< (first-coefficient (car bounds-polys)) 0)
             ;; ((var < c) (c < var)), upper bound lower bound.
             (mv (- (access poly (cadr bounds-polys) :constant))
                 (access poly (cadr bounds-polys) :relation)
                 (access poly (cadr bounds-polys) :ttree)
                 (access poly (car bounds-polys) :constant)
                 (access poly (car bounds-polys) :relation)
                 (access poly (car bounds-polys) :ttree))
             ;; ((c < var) (var < c)), lower bound upper bound.
           (mv (- (access poly (car bounds-polys) :constant))
               (access poly (car bounds-polys) :relation)
               (access poly (car bounds-polys) :ttree)
               (access poly (cadr bounds-polys) :constant)
               (access poly (cadr bounds-polys) :relation)
               (access poly (cadr bounds-polys) :ttree))))))

(defun good-bounds-in-pot (var pot-lst pt)

; Is bds good enough for deal-with-division?  That is, can we use
; the information in pot-lst to bound var either away from zero or
; at zero?

; This information is needed in deal-with-division where we may,
; for instance, multiply x and (/ x).  If we know that x is non-zero,
; their product will be equal to one.  If we know that x is zero, their
; product is equal to zero.

  (let ((bounds-polys (bounds-polys-with-var var
                                             pot-lst
                                             pt)))
    (mv-let (var-lbd var-lbd-rel var-lbd-ttree
             var-ubd var-ubd-rel var-ubd-ttree)
            (extract-bounds bounds-polys)
    (declare (ignore var-lbd-ttree var-ubd-ttree))
    (or (and (eql var-lbd 0)
             (eql var-ubd 0))
        (and var-lbd
             (< 0 var-lbd))
        (and (eql var-lbd 0)
             (eq var-lbd-rel '<))
        (and var-ubd
             (< var-ubd 0))
        (and (eql var-ubd 0)
             (eq var-ubd-rel '<))))))

(defun inverse-polys (var inv-var pot-lst ttree pt)

; Var and inv-var are as in add-inverse-polys.  Ttree is the ttree
; from the call to type-set in inverse-polys.

; Bounds-polys-for-var extracts any bounds polys from pot-lst.
; Extract-bounds deconstructs any bounds polys found.  This
; information is then used to try to tighten up our knowledge about
; both var and inv-var.  We return a list of bounds polys constructed
; using this information.

; A couple of simple examples will help to understand what we are doing:
; 1. If we can determine that (< 4 x), we can add both (< 0 (/ x)) and
; (< (/ x) 1/4).
; 2. If we can determine that (< 0 x) and (< x 4), we can add
; (< 0 (/ x)) and (< (/ x) 1/4).
; 3. If we can only determine that (< -2 x), we cannot add anything about
; (/ x) to the pot-lst.

; We handle the symmetric cases for negative x.

  (if (and (good-pot-varp var)
           (good-pot-varp inv-var))
      (let ((bounds-polys-for-var
             (bounds-polys-with-var var pot-lst pt))
            (bounds-polys-for-inv-var
             (bounds-polys-with-var inv-var pot-lst pt)))
        (mv-let (var-lbd var-lbd-rel var-lbd-ttree
                 var-ubd var-ubd-rel var-ubd-ttree)
          (extract-bounds bounds-polys-for-var)
          (mv-let (inv-var-lbd inv-var-lbd-rel inv-var-lbd-ttree
                   inv-var-ubd inv-var-ubd-rel inv-var-ubd-ttree)
            (extract-bounds bounds-polys-for-inv-var)
            (cond
             ((and (or (eql var-lbd 0)
                       (eql inv-var-lbd 0))
                   (or (eql var-ubd 0)
                       (eql inv-var-ubd 0)))

; Assume that all four relations are <=.  That is a weaker assumption
; than whatever is really the case.  From that assumption, we conclude
; that var and inv-var are 0.  We make sure that this is recorded in
; the pot-lst.  If the actual case is that one of the relations is a
; strict <, then the case is contradictory and we can add any other
; polys we want, including these.  Note that at least two of the four
; polys we are about to add are already in the pot-lst.

              (list
               ;; 0 <= var
               (add-linear-terms :rhs var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             (cons-tag-trees var-lbd-ttree
                                                             inv-var-lbd-ttree))
                                            '<=
                                            t
                                            nil))
               ;; var <= 0
               (add-linear-terms :lhs var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             (cons-tag-trees var-ubd-ttree
                                                             inv-var-ubd-ttree))
                                            '<=
                                            t
                                            nil))
               ;; 0 <= inv-var
               (add-linear-terms :rhs inv-var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             (cons-tag-trees var-lbd-ttree
                                                             inv-var-lbd-ttree))
                                            '<=
                                            t
                                            nil))
               ;; inv-var <= 0
               (add-linear-terms :lhs inv-var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             (cons-tag-trees var-ubd-ttree
                                                             inv-var-ubd-ttree))
                                            '<=
                                            t
                                            nil))))

             ((or (and var-lbd
                       (< 0 var-lbd))
                  (and inv-var-lbd
                       (< 0 inv-var-lbd)))

; We try to gather bounds polys in four stages --- a lower bound for inv-var,
; a lower bound for var, an upper bound for inv-var, and an upper bound
; for var.

              (let* ((ttree1 (cons-tag-trees ttree
                                             (cons-tag-trees var-lbd-ttree
                                                             inv-var-lbd-ttree)))

                     (bounds-polys1
                      (cond ((and var-ubd
                                  (not (eql var-ubd 0))
                                  (or (null inv-var-lbd)
                                      (< inv-var-lbd (/ var-ubd))))
                             (list
                              ;; (/ var-ubd) [<,<=] inv-var
                              (add-linear-terms :lhs (kwote (/ var-ubd))
                                                :rhs inv-var
                                                (base-poly (cons-tag-trees
                                                            ttree1
                                                            var-ubd-ttree)
                                                           var-ubd-rel
                                                           t
                                                           nil))))
                            ((null inv-var-lbd)
                             (list
                              ;; 0 < inv-var
                              (add-linear-terms :rhs inv-var
                                                (base-poly ttree1
                                                           '<
                                                           t
                                                           nil))))
                            (t
                             nil)))
                     (bounds-polys2
                      (cond ((and inv-var-ubd
                                  (not (eql inv-var-ubd 0))
                                  (or (null var-lbd)
                                      (< var-lbd (/ inv-var-ubd))))
                             (cons
                              ;; (/ inv-var-ubd) [<,<=] var
                              (add-linear-terms :lhs (kwote (/ inv-var-ubd))
                                                :rhs var
                                                (base-poly (cons-tag-trees
                                                            ttree1
                                                            inv-var-ubd-ttree)
                                                           inv-var-ubd-rel
                                                           t
                                                           nil))
                              bounds-polys1))
                            ((null var-lbd)
                             ;; 0 < var
                             (cons
                              (add-linear-terms :rhs var
                                                (base-poly ttree1
                                                           '<
                                                           t
                                                           nil))
                              bounds-polys1))
                            (t
                             bounds-polys1)))
                     (bounds-polys3
                      (cond ((and var-lbd
                                  (not (eql var-lbd 0))
                                  (or (null inv-var-ubd)
                                      (< (/ var-lbd) inv-var-ubd)))
                             (cons
                              ;; inv-var [<,<=] (/ var-lbd)
                              (add-linear-terms :lhs inv-var
                                                :rhs (kwote (/ var-lbd))
                                                (base-poly ttree1
                                                           var-lbd-rel
                                                           t
                                                           nil))
                              bounds-polys2))
                            (t
                             bounds-polys2)))
                     (bounds-polys4
                      (cond ((and inv-var-lbd
                                  (not (eql inv-var-lbd 0))
                                  (or (null var-ubd)
                                      (< (/ inv-var-lbd) var-ubd)))
                             (cons
                              ;; var [<,<=] (/ inv-var-lbd)
                              (add-linear-terms :lhs var
                                                :rhs (kwote (/ inv-var-lbd))
                                                (base-poly ttree1
                                                           inv-var-lbd-rel
                                                           t
                                                           nil))
                              bounds-polys3))
                            (t
                             bounds-polys3))))
                bounds-polys4))

             ((or (and var-ubd
                       (< var-ubd 0))
                  (and inv-var-ubd
                       (< inv-var-ubd 0)))

; We try to gather bounds polys in four stages --- a upper bound for inv-var,
; a upper bound for var, an lower bound for inv-var, and an lower bound
; for var.

              (let* ((ttree1 (cons-tag-trees ttree
                                             (cons-tag-trees var-ubd-ttree
                                                             inv-var-ubd-ttree)))
                     (bounds-polys1
                      (cond ((and var-lbd
                                  (not (eql var-lbd 0))
                                  (or (null inv-var-ubd)
                                      (< (/ var-lbd) inv-var-ubd)))
                             (list
                              ;; inv-var [<,<=] (/ var-lbd)
                              (add-linear-terms :lhs inv-var
                                                :rhs (kwote (/ var-lbd))
                                                (base-poly (cons-tag-trees
                                                            ttree1
                                                            var-lbd-ttree)
                                                           var-lbd-rel
                                                           t
                                                           nil))))
                            ((null inv-var-ubd)
                             (list
                              ;; inv-var < 0
                              (add-linear-terms :lhs inv-var
                                                (base-poly ttree1
                                                           '<
                                                           t
                                                           nil))))
                            (t
                             nil)))
                     (bounds-polys2
                      (cond ((and inv-var-lbd
                                  (not (eql inv-var-lbd 0))
                                  (or (null var-ubd)
                                      (< (/ inv-var-lbd) var-ubd)))
                             (cons
                              ;; var [<,<=] (/ inv-var-lbd)
                              (add-linear-terms :lhs var
                                                :rhs (kwote (/ inv-var-lbd))
                                                (base-poly (cons-tag-trees
                                                            ttree1
                                                            inv-var-lbd-ttree)
                                                           var-lbd-rel
                                                           t
                                                           nil))
                              bounds-polys1))
                            ((null var-ubd)
                             ;; var < 0
                             (cons
                              (add-linear-terms :lhs var
                                                (base-poly ttree1
                                                           '<
                                                           t
                                                           nil))
                              bounds-polys1))
                            (t
                             bounds-polys1)))
                     (bounds-polys3
                      (cond ((and var-ubd
                                  (not (eql var-ubd 0))
                                  (or (null inv-var-lbd)
                                      (< inv-var-lbd (/ var-ubd))))
                             (cons
                              ;; (/ var-ubd) [<,<=] inv-var
                              (add-linear-terms :lhs (kwote (/ var-ubd))
                                                :rhs inv-var
                                                (base-poly ttree1
                                                           var-ubd-rel
                                                           t
                                                           nil))
                              bounds-polys2))
                            (t
                             bounds-polys2)))
                     (bounds-polys4
                      (cond ((and inv-var-ubd
                                  (not (eql inv-var-ubd 0))
                                  (or (null var-lbd)
                                      (< var-lbd (/ inv-var-ubd))))
                             (cons
                              ;; (/ inv-var-ubd) [<,<=] var
                              (add-linear-terms :lhs (kwote (/ inv-var-ubd))
                                                :rhs var
                                                (base-poly ttree1
                                                           inv-var-ubd-rel
                                                           t
                                                           nil))
                              bounds-polys3))
                            (t
                             bounds-polys3))))
                bounds-polys4))

             ((and (eql var-lbd 0)
                   (eq var-lbd-rel '<))
              ;; 0 < inv-var
              (list
               (add-linear-terms :rhs inv-var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             var-lbd-ttree)
                                            '<
                                            t
                                            nil))))
             ((and (eql inv-var-lbd 0)
                   (eq inv-var-lbd-rel '<))
              ;; 0 < var
              (list
               (add-linear-terms :rhs var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             inv-var-lbd-ttree)
                                            '<
                                            t
                                            nil))))
             ((and (eql var-ubd 0)
                   (eq var-ubd-rel '<))
              ;; inv-var < 0
              (list
               (add-linear-terms :lhs inv-var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             var-ubd-ttree)
                                            '<
                                            t
                                            nil))))
             ((and (eql inv-var-ubd 0)
                   (eq inv-var-ubd-rel '<))
              ;; var < 0
              (list
               (add-linear-terms :lhs var
                                 (base-poly (cons-tag-trees
                                             ttree
                                             inv-var-ubd-ttree)
                                            '<
                                            t
                                            nil))))
             (t
              nil)))))
    (er hard 'inverse-polys
        "A presumptive pot-label, ~x0,  has turned out to be illegitimate. ~
         If possible, please send a script reproducing this error ~
         to the authors of ACL2."
        (if (good-pot-varp var)
            inv-var
          var))))

(defun add-inverse-polys (var
                          type-alist wrld
                          simplify-clause-pot-lst
                          force-flg ens pt)

; If var is of the form
; 1. (/ x) or (expt (/ x) n) and x is rational, or
; 2. (expt x c) or (expt x (* c y)), where c is a negative integer
;    and x is rational,
; we try to find bounds for either var or its multiplicative inverse and
; then use any bounds found to bound the other.  The work of gathering
; the polys is done in inverse-polys.

  (if (var-with-divisionp var)
      (let ((inverted-var (invert-var var)))
        (mv-let (base-ts base-ttree)
                (type-set inverted-var
                          force-flg
                          nil ; dwp
                          type-alist
                          ens
                          wrld
                          nil ; ttree
                          nil ; pot-lst
                          nil) ; pt
                (if (ts-real/rationalp base-ts)
                    (let ((inverse-polys
                           (inverse-polys var
                                          inverted-var
                                          simplify-clause-pot-lst
                                          base-ttree
                                          pt)))
                      (add-polys inverse-polys
                                 simplify-clause-pot-lst
                                 pt
                                 t ; nonlinearp hint
                                 type-alist
                                 ens
                                 force-flg
                                 wrld))
                  (mv nil simplify-clause-pot-lst))))
    (mv nil simplify-clause-pot-lst)))

(defun add-polys-from-type-set (var pot-lst type-alist
                                    pt force-flg ens wrld)

; At the time of this writing, this function is called only from
; add-polys-and-lemmas3.  When doing non-linear arithmetic, we
; have found this extra information gathering useful.

; Warning: This function should not be used with any terms that are
; not legitimate pot-vars.  See the definition of good-pot-varp.
; Assuming that term is a legitimate pot-label --- meets all the
; invariants --- we do not have to normalize any of the polys below.
; It would, however, not be very expensive to wrap the below in a call
; to normalize-poly-lst.

  (if (good-pot-varp var)
      (add-polys (polys-from-type-set var
                                      force-flg
                                      nil   ; dwp
                                      type-alist
                                      ens
                                      wrld
                                      nil)  ; ttree
                 pot-lst
                 pt
                 t ; nonlinearp hint
                 type-alist
                 ens
                 force-flg
                 wrld)
    (mv (er hard 'add-polys-from-type-set
        "A presumptive pot-label, ~x0,  has turned out to be illegitimate. ~
         If possible, please send a script  reproducing this error ~
         to the authors of ACL2."
        var)
        nil)))

(defun length-of-shortest-polys-with-var (poly-lst pt n)

; Poly-lst is a list of polys, pt is a parent tree of polys to be
; ignored, and n is the length of the shortest alist found so far, or
; t if we haven't found any yet.  We cdr down pot-lst looking for a
; poly whose alist is shorter than n, and return the length of the
; shortest alist found.

  (cond ((null poly-lst)
         n)
        ((and (or (eq n t)
                  (< (length (access poly (car poly-lst) :alist)) n))
              (not (ignore-polyp (access poly (car poly-lst) :parents) pt)))
         (length-of-shortest-polys-with-var (cdr poly-lst) pt
                                            (length (access poly
                                                            (car poly-lst)
                                                            :alist))))
        (t
         (length-of-shortest-polys-with-var (cdr poly-lst) pt n))))

(defun shortest-polys-with-var1 (poly-lst pt n)
  (cond ((or (null poly-lst)
             (eq n t))
         nil)
        ((and (or (equal (length (access poly (car poly-lst) :alist)) n)
                  (equal (length (access poly (car poly-lst) :alist)) (+ n 1)))
              (not (ignore-polyp (access poly (car poly-lst) :parents) pt)))
         (cons (car poly-lst)
               (shortest-polys-with-var1 (cdr poly-lst) pt n)))
        (t
         (shortest-polys-with-var1 (cdr poly-lst) pt n))))

(defun shortest-polys-with-var (var pot-lst pt)

; Var is a pot-label in pot-lst and pt is a parent tree of polys to ignore.
; We return a list of the polys with the shortest alists in the pot
; labeled with var.  These polys can be considered as the ``simplest''
; polys about var.

  (cond ((null pot-lst)
         nil)
        ((equal var (access linear-pot (car pot-lst) :var))

; We have found the pot we are looking for.  We find the length of the
; shortest polys in the pot.  We then find all the polys in the pot
; with alists of that length, and return a list of those polys.

         (let ((n (length-of-shortest-polys-with-var
                   (append (access linear-pot
                                   (car pot-lst)
                                   :negatives)
                           (access linear-pot
                                   (car pot-lst)
                                   :positives))
                   pt
                   t)))
           (append (shortest-polys-with-var1
                    (access linear-pot (car pot-lst) :negatives)
                    pt n)
                   (shortest-polys-with-var1
                    (access linear-pot (car pot-lst) :positives)
                    pt n))))
        (t (shortest-polys-with-var var (cdr pot-lst) pt))))

(defun binary-*-leaves (term)
  (if (eq (fn-symb term) 'BINARY-*)
      (cons (fargn term 1)
            (binary-*-leaves (fargn term 2)))
    (list term)))

(defun binary-*-tree (leaves)

; Return the BINARY-* term with leaves at its tips.  In practice,
; leaves always contains at least two elements.

  (cond ((null (cdr leaves))
         (car leaves))
        ((null (cddr leaves))
         (cons-term 'BINARY-*
                    (list
                     (car leaves)
                     (cadr leaves))))
        (t
         (cons-term 'BINARY-*
                    (list
                     (car leaves)
                     (binary-*-tree (cdr leaves)))))))

(defun merge-arith-term-order (l1 l2)
  (cond ((null l1) l2)
        ((null l2) l1)
        ((arith-term-order (car l2) (car l1))
         (cons (car l2) (merge-arith-term-order l1 (cdr l2))))
        (t (cons (car l1) (merge-arith-term-order (cdr l1) l2)))))

(defun insert-arith-term-order (item list)
  (cond ((null list)
         (list item))
        ((arith-term-order item (car list))
         (cons item list))
        (t
         (cons (car list)
               (insert-arith-term-order item (cdr list))))))

(defun sort-arith-term-order (list)
  (cond ((null list)
         nil)
        (t
         (insert-arith-term-order (car list)
                                  (sort-arith-term-order (cdr list))))))

(defun multiply-alist-and-const (alist const poly)
  (cond ((null alist)
         poly)
        (t
         (let ((temp-poly (add-linear-term (cons-term 'BINARY-*
                                                      (list
                                                       (kwote (* const
                                                                 (cdar alist)))
                                                       (caar alist)))
                                           'rhs
                                           poly)))
           (multiply-alist-and-const (cdr alist)
                                     const
                                     temp-poly)))))

(defun collect-rational-poly-p-lst (poly-lst)
  (cond ((endp poly-lst) nil)
        ((access poly (car poly-lst) :rational-poly-p)
         (cons (car poly-lst)
               (collect-rational-poly-p-lst (cdr poly-lst))))
        (t (collect-rational-poly-p-lst (cdr poly-lst)))))
