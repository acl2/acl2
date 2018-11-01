;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "intersection")

(defun region-p (term)
  (declare (type t term))
  (case-match term
    ((`not x) (trapezoid-p x))
    ((x)      (trapezoid-p x))
    (&        nil)))

(defun negated-region-p (term)
  (declare (type t term))
  (case-match term
    ((`not &) t)
    (&        nil)))

(def::un region-trapezoid (term)
  (declare (xargs :signature ((region-p) trapezoid-p)))
  (case-match term
    ((`not x) x)
    ((x)      x)
    (&        nil)))

(def::un true-region (zoid)
  (declare (xargs :signature ((trapezoid-p) region-p)))
  (list zoid))

(defthm not-negated-region-p-true-region
  (not (negated-region-p (true-region zoid)))
  :rule-classes (:type-prescription
                 (:forward-chaining :trigger-terms ((true-region zoid)))))

(def::un negated-region (zoid)
  (declare (xargs :signature ((trapezoid-p) region-p)))
  `(not ,zoid))

(defthm negated-region-p-negated-region
  (negated-region-p (negated-region zoid))
  :rule-classes (:type-prescription
                 (:forward-chaining :trigger-terms ((negated-region zoid)))))

(defthm region-trapezoid-true-region
  (equal (region-trapezoid (true-region zoid))
         zoid))

(defthm region-trapezoid-negated-region
  (equal (region-trapezoid (negated-region zoid))
         zoid))

;; ---------------------------------------------------------------------------------

(defun eval-region (term env)
  (declare (type t term))
  (case-match term
    ((`not x) (not (eval-ineq-list x env)))
    ((x)      (eval-ineq-list x env))
    (&        nil)))

(defthm alt-eval-region
  (implies
   (region-p term)
   (iff (eval-region term env)
        (if (negated-region-p term)
            (not (eval-ineq-list (region-trapezoid term) env))
          (eval-ineq-list (region-trapezoid term) env)))))
  
(defthm eval-region-false
  (not (eval-region (negated-region nil) env)))

(defthm eval-region-true
  (eval-region (true-region nil) env))

(in-theory (disable (true-region) (negated-region)))

(in-theory (disable eval-region))
(in-theory (disable region-p region-trapezoid true-region negated-region negated-region-p))

(defun wf-region-p (x env)
  (declare (type t x env))
  (and (region-p x)
       (iff (eval-region x env)
            (not (negated-region-p x)))))

(defthm wf-region-implies-region-p
  (implies
   (wf-region-p x env)
   (region-p x))
  :rule-classes (:forward-chaining))

;; ---------------------------------------------------------------------------------

(def::un not-region (term)
  (declare (xargs :signature ((region-p) region-p)))
  (if (negated-region-p term)
      (true-region (region-trapezoid term))
    (negated-region (region-trapezoid term))))

(def::signature not-region ((lambda (x) (wf-region-p x x2))) (lambda (x) (wf-region-p x x2)))

(defthm eval-region-not-region
  (implies
   (region-p term)
   (iff (eval-region (not-region term) env)
        (not (eval-region term env)))))

(in-theory (disable not-region))

;; ---------------------------------------------------------------------------------

(def::un and-regions (x y env)
  (declare (xargs :signature ((region-p region-p env-p) region-p)))
  (if (not (eval-region x env)) x
    (if (not (eval-region y env)) y
      (true-region (and-zoid (region-trapezoid x) (region-trapezoid y) env)))))

(def::signature and-regions ((lambda (x) (wf-region-p x x1)) (lambda (x) (wf-region-p x x1)) env-p) (lambda (x) (wf-region-p x x1)))

(defthm inv1-and-regions
  (implies
   (and
    (wf-region-p x cex)
    (wf-region-p y cex)
    (env-p cex))
   (iff  (eval-region (and-regions x y cex) cex)
         (and
          (eval-region x cex)
          (eval-region y cex)))))

(defthm inv2a-and-regions
  (implies
   (and
    (and
     (wf-region-p x cex)
     (wf-region-p y cex)
     (env-p cex))
    (and
     (eval-region x cex)
     (eval-region y cex))
    (not
     (and
      (eval-region x any)
      (eval-region y any))))
   (not (eval-region (and-regions x y cex) any))))

(defthm inv2b-and-regions
  (implies
   (and
    (and
     (wf-region-p x cex)
     (wf-region-p y cex)
     (env-p cex))
    (not 
     (and
      (eval-region x cex)
      (eval-region y cex)))
    (and
     (eval-region x any)
     (eval-region y any)))
   (eval-region (and-regions x y cex) any)))

(defthm simplify-and-regions
  (implies
   (not (eval-region x env))
   (equal (and-regions x y env) x)))

(defthm simplify-and-regions-2
  (implies
   (not (eval-region y env))
   (equal (and-regions x y env)
          (if (not (eval-region x env)) x y))))

(in-theory (disable and-regions))

;; ---------------------------------------------------------------------------------

(def::un normalize-equal-0 (poly env)
  (declare (xargs :signature ((poly-p env-p) region-p)))
  (let ((const (isConstant poly)))
    (let ((value (eval-poly poly env)))
      (if (equal value 0) 
          (if const (true-region nil)
            (let ((xid (leading-variable poly)))
              (let ((rst (solve xid poly)))
                (let ((r (variableEquality xid rst)))
                  (true-region (list r))))))
        (if const (negated-region nil)
          (if (< value 0) (negated-region (list (solvePolyGreater0 :exclusive (mul -1 poly) env)))
            (negated-region (list (solvePolyGreater0 :exclusive poly env)))))))))

(defthm inv1-normalize-equal-0
  (implies
   (and
    (poly-p poly)
    (env-p cex))
   (iff (eval-region (normalize-equal-0 poly cex) cex)
        (equal (eval-poly poly cex) 0)))
  :hints (("Goal" :in-theory (enable  eval-ineq-polyRelationp))))

(defthm inv2a-normalize-equal-0
  (implies
   (and
    (poly-p poly)
    (env-p cex)
    (equal (eval-poly poly cex) 0)
    (not (equal (eval-poly poly any) 0)))
   (not (eval-region (normalize-equal-0 poly cex) any)))
  :hints (("Goal" :in-theory (enable eval-ineq-polyRelationp))))

(defthm inv2b-normalize-equal-0
  (implies
   (and
    (poly-p poly)
    (env-p cex)
    (not (equal (eval-poly poly cex) 0))
    (equal (eval-poly poly any) 0))
   (eval-region (normalize-equal-0 poly cex) any))
  :hints (("Goal" :in-theory (enable eval-ineq-polyRelationp))))

(defthm wf-region-normalize-equal-0
  (implies
   (and
    (poly-p poly)
    (env-p env))
   (wf-region-p (normalize-equal-0 poly env) env))
  :hints (("Goal" :in-theory (enable eval-ineq-polyRelationp)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((normalize-equal-0 poly env)))))

(in-theory (disable normalize-equal-0))

;; ---------------------------------------------------------------------------------

(def::un normalize-gt-0 (relation poly env)
  (declare (xargs :signature ((relation-p poly-p env-p) region-p)))
  (let ((const (isConstant poly)))
    (let ((value (eval-poly poly env)))
      (if const (if (gt-relation-p relation value) (true-region nil) (negated-region nil))
        (if (gt-relation-p relation value) 
            (true-region (list (solvePolyGreater0 relation poly env)))
          (negated-region (list (solvePolyGreater0 (relation-not relation) (mul -1 poly) env))))))))

(defthm eval-region-normalize-gt-0
  (implies
   (and
    (relation-p relation)
    (poly-p poly)
    (env-p env))
   (iff (eval-region (normalize-gt-0 relation poly env) any)
        (gt-relation-p relation (eval-poly poly any)))))

(defthm wf-region-normalize-gt-0
  (implies
   (and
    (relation-p relation)
    (poly-p poly)
    (env-p env))
   (wf-region-p (normalize-gt-0 relation poly env) env))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((normalize-gt-0 relation poly env)))))

(in-theory (disable normalize-gt-0))

;; ---------------------------------------------------------------------------------

(def::un generalize-ineq (term env)
  (declare (xargs :signature ((t env-p) region-p)))
  (case-match term
    (('and x y)
     (let ((x (generalize-ineq x env))
           (y (generalize-ineq y env)))
       (and-regions x y env)))
    (('or x y)
     (let ((x (generalize-ineq x env))
           (y (generalize-ineq y env)))
       (not-region (and-regions (not-region x) (not-region y) env))))
    (('not x)
     (let ((x (generalize-ineq x env)))
       (not-region x)))
    (('= var poly)
     (let ((x (bound-poly var))
           (y (poly-fix! poly)))
       (normalize-equal-0 (sub x y) env)))
    (('!= var poly)
     (let ((x (bound-poly var))
           (y (poly-fix! poly)))
       (not-region (normalize-equal-0 (sub x y) env))))
    (('< x y)
     (let ((x (bound-poly x))
           (y (poly-fix! y)))
       (normalize-gt-0 :exclusive (sub y x) env)))
    (('<= x y)
     (let ((x (bound-poly x))
           (y (poly-fix! y)))
       (normalize-gt-0 :inclusive (sub y x) env)))
    (('> x y)
     (let ((x (bound-poly x))
           (y (poly-fix! y)))
       (normalize-gt-0 :exclusive (sub x y) env)))
    (('>= x y)
     (let ((x (bound-poly x))
           (y (poly-fix! y)))
       (normalize-gt-0 :inclusive (sub x y) env)))
    (& (negated-region nil))))

(include-book "arithmetic-5/top" :dir :system)

(defthm inv1-generalize-ineq
  (implies
   (env-p env)
   (and (wf-region-p (generalize-ineq term env) env)
        (iff (eval-region (generalize-ineq term env) env)
             (eval-ineq term env))))
  :hints (("Goal" :induct (generalize-ineq term env)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable eval-ineq)))))
 
(def::signature generalize-ineq (t env-p) (lambda (x) (wf-region-p x x1))
  :hints (("Goal" :in-theory (disable wf-region-p))))

(in-theory (disable wf-region-p alt-eval-region))

(defthm inv2-generalize-ineq
  (implies
   (and
    (env-p env)
    (iff (eval-ineq term env)
         (not (eval-ineq term any))))
   (iff (eval-region (generalize-ineq term env) any)
        (eval-ineq term any)))
  :hints (("Goal" :induct (generalize-ineq term env)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable eval-ineq)))))
