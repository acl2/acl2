;; 
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;; 
;; 
(in-package "ACL2")
(include-book "coi/util/defun" :dir :system)
(include-book "coi/quantification/quantification" :dir :system)
(include-book "coi/util/deffix" :dir :system)
(include-book "coi/util/good-rewrite-order" :dir :system)

;; ---------------------------------------------------------------------

(in-theory 
 (disable 
  BAG::MEMBERP-CAR-WHEN-DISJOINT
  BAG::SUBBAGP-REMOVE-BAG-APPEND
  BAG::SUBBAGP-IMPLIES-MEMBERSHIP
  BAG::DISJOINT-COMMUTATIVE
  BAG::DISJOINT-OF-APPEND-ONE
  LIST::DISJOINT-REMOVE-DEFINITION
  BAG::REMOVE-BAG-DOES-NOTHING
  list::disjoint
  BAG::SUBBAGP-IMPLIES-SUBBAGP-CONS
  BAG::SUBBAGP-APPEND-2
  BAG::DISJOINT-OF-APPEND-TWO
  BAG::REMOVE-BAG-OF-CONS
  BAG::MEMBERP-SUBBAGP
  BAG::SUBBAGP-SELF
  BAG::SUBBAGP-IMPLIES-SUBBAGP-APPEND-CAR
  BAG::SUBBAGP-IMPLIES-SUBBAGP-APPEND-REC
  BAG::COUNT-<-0-REWRITE
  BAG::COUNT-WHEN-MEMBERP
  BAG::COUNT-OF-APPEND
  BAG::COUNT-WHEN-NON-MEMBER
  BAG::COUNT-0-FOR-NON-MEMBERP 
  ))

;; ---------------------------------------------------------------------

(defun consp-equiv (x y)
  (declare (type t x y))
  (iff (consp x) (consp y)))

(defequiv consp-equiv)

(defcong consp-equiv equal (consp x) 1)

;; We leave it enabled since we don't actually use it for anything interesting ..

;; This is what we want to prove for each new list-like equivalence relation
(defrefinement list-equiv consp-equiv)

;; ---------------------------------------------------------------------

(def::un-skd set-equiv-quant (x y)
  (forall (a) (equal (list::memberp a x)
                     (list::memberp a y))))

(verify-guards set-equiv-quant)

(defequiv set-equiv-quant
  :hints ((quant::inst?)))

(defcong set-equiv-quant equal (list::memberp a x) 2
  :hints ((quant::inst?)))

(defrefinement list-equiv set-equiv-quant)

(encapsulate
 ()

 (encapsulate
  (((set-equiv-hyps) => *)
   ((set-equiv-left) => *)
   ((set-equiv-right) => *))

  (local (defun set-equiv-hyps () nil))
  (local (defun set-equiv-left () nil))
  (local (defun set-equiv-right () nil))

  (defthm set-equiv-multiplicity-constraint
    (implies
     (set-equiv-hyps)
     (equal (list::memberp arbitrary-varid (set-equiv-left))
            (list::memberp arbitrary-varid (set-equiv-right))))
    :rule-classes nil)
  )

 (defthm set-equiv-by-multiplicity-driver
   (implies (set-equiv-hyps)
            (set-equiv-quant (set-equiv-left) (set-equiv-right)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        set-equiv-multiplicity-constraint
                        (arbitrary-varid hide)))))))

 (ADVISER::defadvice ADVISER::set-equiv-by-multiplicity
   (implies (set-equiv-hyps)
            (set-equiv (set-equiv-left) (set-equiv-right)))
   :rule-classes (:pick-a-point :driver set-equiv-by-multiplicity-driver))

 )

(defcong set-equiv-quant set-equiv-quant (cons a x) 2
  :hints (("Goal" :in-theory (enable list::memberp))))

(defcong set-equiv-quant set-equiv-quant (append x y) 1)
(defcong set-equiv-quant set-equiv-quant (append x y) 2)

(defthm set-equiv-quant-cons-commutes
  (set-equiv-quant (cons a (cons b x))
                   (cons b (cons a x))))

(defthm set-equiv-quant-append-commutes
  (set-equiv-quant (append x y)
                   (append y x)))

(defthm set-equiv-quant-append-append-commute
  (set-equiv-quant (append x (append y z))
                   (append y (append x z))))

(defthm set-equiv-quant-append-cons-commutes-1
  (set-equiv-quant (append (cons a x) y)
                   (cons a (append x y))))

(defthm set-equiv-quant-append-cons-commutes-2
  (set-equiv-quant (append y (cons a x))
                   (cons a (append y x))))

(defthm set-equiv-quant-append-x-append-x
  (set-equiv-quant (append x (append x y))
                   (append x y)))

(defthm set-equiv-quant-append-x-x
  (set-equiv-quant (append x x) x))

(defthm set-equiv-quant-cons-a-cons-a
  (set-equiv-quant (cons a (cons a x))
                   (cons a x)))

;; I don't think we really use this ..
(def::fix set-fix
  set-equiv-quant
  )

(local
 (encapsulate
     ()
   (set-tau-auto-mode nil)
   (defund set-equiv-context (x) 
     (declare (ignore x)) t)
   (in-theory (disable (:type-prescription set-equiv-context)))
   (set-tau-auto-mode t)
   
   ;; So .. there is an issue with forward-chaining off of an
   ;; equivalence relation .. it is not symmetric so it doesn't
   ;; account for commuted instances.  This is an experiement
   ;; to identify objects that are probably appear as arguments
   ;; to an equiv relation.
   (defthm identify-set-equiv-context
     (implies
      (set-equiv-quant x y)
      (and (set-equiv-context x)
           (set-equiv-context y)))
     :rule-classes (:forward-chaining)
     :hints (("Goal" :in-theory (enable set-equiv-context))))
   
   (defmacro iff-conjunction (x y)
     `(and (or (not ,x) ,y)
           (or ,x (not ,y))))
   
   (defthm set-equiv-implies-memberp-equiv
     (implies
      (and
       (set-equiv-context y)
       (set-equiv-quant x y))
      (iff-conjunction (list::memberp a y)
                       (list::memberp a x)))
     :rule-classes ((:forward-chaining :trigger-terms ((list::memberp a x)))))
   
   (defthm consp-implies-memberp-car
     (implies
      (consp x)
      (list::memberp (car x) x))
     :rule-classes (:type-prescription :forward-chaining))
   
   (defthm memberp-implies-consp
     (implies
      (list::memberp a x)
      (consp x))
     :rule-classes (:forward-chaining))
   
   ))

(defrefinement set-equiv-quant consp-equiv)

;; ---------------------------------------------------------------------

;; (encapsulate
;;     (
;;      ((fn * *) => *)
;;      ((fixx *) => *)
;;      ((equiv * *) => *)
;;      )
;;   (local (defun fixx (x) x))
;;   (local (defun equiv (x y) (equal x y)))
;;   (local (defun fn (a b) (list a b)))
;;   (defequiv equiv)
;;   (defthm equiv1-implies-equiv2-fn
;;     (implies
;;      (syntaxp (symbolp x))
;;      (equiv (fn x a) (fn (fixx x) a))))
;;   )

;; (defthm fn-cong
;;   (implies
;;    (equal (fixx x) (fixx y))
;;    (equiv (fn x a) (fn y a))))

(defthm member-remove-equal
  (equal (list::memberp a (remove-equal b x))
         (if (equal a b) nil
           (list::memberp a x))))

(defthm remove-non-member
  (implies
   (not (list::memberp a list))
   (equal (remove-equal a list)
          (list-fix list))))

(defcong set-equiv-quant set-equiv-quant (remove-equal a x) 2)

(defthm remove-equal-commutes
  (equal (remove-equal a (remove-equal b list))
         (remove-equal b (remove-equal a list))))

(defthm remove-remove
  (equal (remove-equal a (remove-equal a x))
         (remove-equal a x)))

(defthm len-remove-equal
  (implies
   (list::memberp a list)
   (< (len (remove-equal a list))
      (len list)))
  :rule-classes (:linear))

;; ---------------------------------------------------------------------

(def::un set-insert (a list)
  (declare (xargs :signature ((t true-listp) true-listp)
                  :congruence ((nil set-equiv-quant) set-equiv-quant)))
  (if (list::memberp a list) list
    (cons a list)))

(defthm list::memberp-set-insert
  (equal (list::memberp a (set-insert b list))
         (or (equal a b)
             (list::memberp a list))))

(in-theory (disable set-insert))

;; ---------------------------------------------------------------------

(def::un set-size (list)
  (declare (xargs :signature ((t) natp)
                  :guard (true-listp list)
                  :measure (len list)))
  (if (not (consp list)) 0
    (1+ (set-size (remove-equal (car list) list)))))

(defthmd open-set-size-on-memberp
  (implies
   (list::memberp a list)
   (equal (set-size list)
          (1+ (set-size (remove-equal a list)))))
  :hints (("Goal" :induct (set-size list)
           :expand (list::memberp a list))))


(defun x-y-set-induction (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (x-y-set-induction (remove-equal (car x) x)
                         (remove-equal (car x) y))
    (list x y)))
    
(encapsulate
    ()

  (local (in-theory (enable open-set-size-on-memberp)))
  
  (local
   (defthm memberp-car-remove-equal
     (implies
      (and
       (consp x)
       (not (equal (car x) a)))
      (list::memberp (car x) (remove-equal a x)))
     :rule-classes ((:forward-chaining :trigger-terms ((remove-equal a x))))))
  
  (defcong set-equiv-quant equal (set-size x) 1
    :hints (("Goal" :induct (x-y-set-induction x x-equiv))
            (and stable-under-simplificationp
                 '(:cases ((equal (car x) (car x-equiv)))))))

  )

(defthmd set-size-remove-equal
  (equal (set-size (remove-equal a x))
         (if (list::memberp a x) (1- (set-size x))
           (set-size x))))
   
(local
 (encapsulate
     ()

   (local (in-theory (enable set-size-remove-equal)))

   (defthm set-size-cons
     (equal (set-size (cons a x))
            (if (list::memberp a x) (set-size x)
              (1+ (set-size x))))
     :hints (("Goal" :do-not-induct t :expand (set-size (cons a x)))))
   
   (defthm set-size-set-insert
     (equal (set-size (set-insert a x))
            (if (list::memberp a x) (set-size x)
              (1+ (set-size x))))
     :hints (("Goal" :in-theory (enable set-insert))))
   
   (defthm set-size-cdr
     (equal (set-size (cdr x))
            (if (not (consp x)) 0
              (if (list::memberp (car x) (cdr x)) (set-size x)
                (1- (set-size x))))))

   ))

(defun set-size-equiv (x y)
  (equal (set-size x) (set-size y)))

(defequiv set-size-equiv)
(defrefinement set-equiv-quant set-size-equiv)

(defcong set-size-equiv equal (set-size x) 1)

(in-theory (disable set-size-equiv))

(theory-invariant (incompatible (:rewrite open-set-size-on-memberp)
                                (:rewrite set-size-remove-equal)))

(in-theory (enable set-size-remove-equal))

;; ---------------------------------------------------------------------

(def::un-skd subset-p (x y)
  (forall (a) (implies
               (list::memberp a x)
               (list::memberp a y))))

(verify-guards subset-p)

(defthm memberp-from-memberp-subset
  (implies
   (and
    (subset-p x y)
    (list::memberp a x))
   (list::memberp a y))
  :rule-classes (:forward-chaining)
  :hints ((quant::inst?)))

(encapsulate
 ()

 (encapsulate
  (((subset-p-hyps) => *)
   ((subset-p-left) => *)
   ((subset-p-right) => *))

  (local (defun subset-p-hyps () nil))
  (local (defun subset-p-left () nil))
  (local (defun subset-p-right () nil))

  (defthm subset-p-multiplicity-constraint
    (implies
     (subset-p-hyps)
     (implies
      (list::memberp arbitrary-varid (subset-p-left))
      (list::memberp arbitrary-varid (subset-p-right))))
    :rule-classes nil)
  )

 (defthm subset-p-by-multiplicity-driver
   (implies (subset-p-hyps)
            (subset-p (subset-p-left) (subset-p-right)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        subset-p-multiplicity-constraint
                        (arbitrary-varid hide)))))))

 (ADVISER::defadvice ADVISER::subset-p-by-multiplicity
   (implies (subset-p-hyps)
            (subset-p (subset-p-left) (subset-p-right)))
   :rule-classes (:pick-a-point :driver subset-p-by-multiplicity-driver))

 (in-theory (disable (ADVISER-SUBSET-P-TRIGGER)))

 )

(defcong set-equiv-quant iff (subset-p x y) 1
  :hints ((quant::inst?)))

(defcong set-equiv-quant iff (subset-p x y) 2
  :hints ((quant::inst?)))

(defthm subset-p-identity
  (subset-p x x))

(encapsulate
    ()

  (local
   (defthm equal-booleanp
     (implies
      (booleanp x)
      (iff (equal x y)
           (and (booleanp y)
                (iff x y)))))
   )

  (defthmd set-equiv-double-containment
    (iff (set-equiv-quant x y)
         (and (subset-p x y)
              (subset-p y x)))
    :hints ((quant::inst?)))
  )

(defthm subsetp-remove-equal
  (subset-p (remove-equal a x) x)
  :rule-classes (:rewrite))

(defthm subset-p-append-cons-backchaining-1
  (implies
   (subset-p (append x y) z)
   (subset-p (append x y) (cons a z))))

(defthm subset-p-append-append-backchaining-1
  (implies
   (and
    (syntaxp (not (equal w y)))
    (subset-p (append w x) z))
   (subset-p (append w x) (append y z)))
  :hints ((quant::inst?)))

(defthm subset-p-cons-cons
  (implies
   (subset-p x y)
   (subset-p (cons a x) (cons a y))))

(defthm subset-p-append-append
  (implies
   (subset-p y z)
   (subset-p (append x y) (append x z))))

(defthm subsetp-append-id
  (and (subset-p x (append x y))
       (subset-p x (append y x))))

(defthm subsetp-cons-id
  (subset-p x (cons a x)))

(defthm subsetp-nil
  (subset-p nil x))

(encapsulate
    ()

  (local
   (defthm not-consp-implies-no-members
     (implies
      (not (consp x))
      (not (list::memberp a x)))))

  (defthm subset-not-consp
    (implies
     (not (consp y))
     (iff (subset-p x y)
          (not (consp x))))
    :hints (("Goal" :in-theory (disable (:type-prescription consp-implies-memberp-car)))))

  )

(defun set-subtract (x y)
  (if (not (consp y)) x
    (let ((x (remove-equal (car y) x)))
      (set-subtract x (cdr y)))))

(defthm member-set-subtract
  (iff (list::memberp a (set-subtract x y))
       (and (list::memberp a x)
            (not (list::memberp a y)))))

(defthm subset-set-subtract
  (subset-p (set-subtract x y) x)
  :rule-classes ((:forward-chaining :trigger-terms ((set-subtract x y)))))

;; ---------------------------------------------------------------------

(def::un-sk empty-p (x)
  (forall (a) (not (list::memberp a x))))

(encapsulate
    ()

  (local
   (defthm consp-is-memberp-car
     (iff (consp x)
          (list::memberp (car x) x))))
  
  (local
   (in-theory (disable 
               BAG::SUBBAGP-IMPLIES-MEMBERSHIP
               BAG::MEMBERP-CAR-WHEN-DISJOINT LIST::MEMBERP-CAR
               default-car BAG::DISJOINT-SELF-MEANS-NOT-CONSP list::memberp)))
  
  (defthmd consp-is-not-empty-p
    (iff (consp x)
         (not (empty-p x)))
    :hints ((quant::inst?)))

  )


