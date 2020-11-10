;;
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "ACL2")
(include-book "poly")

(def::type+ lt-op-p (op)
  (or (equal op '<)
      (equal op '<=)))

(defthm implies-not-lt-op
  (implies
   (and
    (not (equal op '<))
    (not (equal op '<=)))
   (not (lt-op-p op)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable lt-op-p))))

(def::type+ gt-op-p (op)
  (declare (type t op))
  (or (equal op '>)
      (equal op '>=)))

(defthm implies-not-gt-op
  (implies
   (and
    (not (equal op '>))
    (not (equal op '>=)))
   (not (gt-op-p op)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable gt-op-p))))

(defthm lt-gt-inconsistent
  (implies
   (and
    (lt-op-p x)
    (gt-op-p x))
   nil)
  :rule-classes (:forward-chaining))

(defund ineq-op-p (op)
  (declare (type t op))
  (or (lt-op-p op)
      (gt-op-p op)))

(defthm ineq-op-implication
  (implies
   (ineq-op-p op)
   (or (lt-op-p op)
       (gt-op-p op)))
  :rule-classes (:forward-chaining))

(defthm implies-not-ineq-op
  (implies
   (and
    (not (lt-op-p op))
    (not (gt-op-p op)))
   (not (ineq-op-p op)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable ineq-op-p))))

(def::un similarInequalities (op1 op2)
  (declare (xargs :signature ((ineq-op-p ineq-op-p) booleanp)))
  (iff (gt-op-p op1) (gt-op-p op2)))

(defthm lt-op-implies-ineq-op
  (implies
   (lt-op-p op)
   (ineq-op-p op))
  :hints (("Goal" :in-theory (enable ineq-op-p)))
  :rule-classes (:forward-chaining))

(defthm gt-op-implies-ineq-op
  (implies
   (gt-op-p op)
   (ineq-op-p op))
  :hints (("Goal" :in-theory (enable ineq-op-p)))
  :rule-classes (:forward-chaining))

(def::type+ eq-op-p (op)
  (equal op '=))

(def::type+ op-p (op)
  (declare (xargs :type-name op
                  :type-witness '=))
  (or (  eq-op-p op)
      (ineq-op-p op)))

(fty::deffixtype op
  :pred   op-p
  :fix    op-fix
  :equiv  op-equiv
  :define nil
  )

(defthm implies-not-op-p
  (implies
   (and
    (not (  eq-op-p op))
    (not (ineq-op-p op)))
   (not (op-p op)))
  :hints (("Goal" :in-theory (enable op-p)))
  :rule-classes (:type-prescription))

(defund inclusive-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '<=) t)
   ((equal op '>=) t)
   (t nil)))

(defund exclusive-op-p (op)
  (declare (type t op))
  (cond
   ((equal op '<) t)
   ((equal op '>) t)
   (t nil)))

;; (defund optype-p (x)
;;   (declare (type t x))
;;   (or (equal x :and)
;;       (equal x :or)))

;; (def::und fix-optype (x)
;;   (declare (xargs :signature ((t) optype-p)))
;;   (if (optype-p x) x
;;     :and))

;; (defthm optype-p-fix-optype
;;   (implies
;;    (optype-p x)
;;    (equal (fix-optype x) x))
;;   :hints (("Goal" :in-theory (enable fix-optype))))

(defund relation-p (x)
  (declare (type t x))
  (or (equal x :inclusive)
      (equal x :exclusive)))

;; If x is more restrictive than y return -1
(def::un compareWith (x y)
  (declare (xargs :signature ((relation-p relation-p) tri-p)))
  (if (equal x y) 0
    (if (equal x :exclusive) -1
      1)))

(def::und fix-relation (x)
  (declare (xargs :signature ((t) relation-p)))
  (if (relation-p x) x
    :inclusive))

(def::un relation-not (x)
  (declare (xargs :signature ((t) relation-p)))
  (if (equal (fix-relation x) :inclusive)
      :exclusive
    :inclusive))

(defthm relation-p-fix-relation
  (implies
   (relation-p x)
   (equal (fix-relation x) x))
  :hints (("Goal" :in-theory (enable fix-relation))))

(def::und gt-relation-p (relation sig)
  (declare (xargs :signature ((relation-p rationalp) booleanp)))
  (let ((relation (fix-relation relation))
        (sig      (rfix sig)))
    (or (< 0 sig) (and (equal relation :inclusive) (= 0 sig)))))

(def::und lt-relation-p (relation sig)
  (declare (xargs :signature ((relation-p rationalp) booleanp)))
  (let ((relation (fix-relation relation))
        (sig      (rfix sig)))
    (or (< sig 0) (and (equal relation :inclusive) (= 0 sig)))))

(defthm gt-relation-p-negate
  (implies
   (rationalp sig)
   (iff (gt-relation-p relation (- sig))
        (lt-relation-p relation sig)))
  :hints (("Goal" :in-theory (enable gt-relation-p lt-relation-p))))

(def::und op-relation (op)
  (declare (xargs :signature ((op-p) relation-p)))
  (cond
   ((equal op '<=) :inclusive)
   ((equal op '>=) :inclusive)
   ((equal op '=)  :inclusive)
   ((equal op '<)  :exclusive)
   ((equal op '>)  :exclusive)
   (t              :exclusive)))

(def::un relative-op (relation op)
  (declare (xargs :signature ((relation-p op-p) op-p)))
  (cond
   ((equal op '<=) (if (eql relation :inclusive) '<= '<))
   ((equal op '>=) (if (eql relation :inclusive) '>= '>))
   ((equal op '=)  '=)
   ((equal op '<)  (if (eql relation :inclusive) '<= '<))
   ((equal op '>)  (if (eql relation :inclusive) '>= '>))
   (t              nil)))

;; ==========================================

(defun polyRelation-p (term)
  (declare (type t term))
  (case-match term
    ((op x y) (and (op-p op) (bound-poly-p x) (poly-p y)))
    (& nil)))

(def::un relation-bound-poly (term)
  (declare (xargs :signature ((polyRelation-p) bound-poly-p)))
  (case-match term
    ((& x &) (bound-poly-fix x))
    (& (bound-poly-witness))))

(def::signature relation-bound-poly (t) bound-poly-p)

(def::un relation-bounding-poly (term)
  (declare (xargs :signature ((polyRelation-p) poly-p)))
  (case-match term
    ((& & y) (poly-fix y))
    (& (poly 0 nil))))

(def::signature relation-bounding-poly (t) poly-p)

(def::un relation-op (term)
  (declare (xargs :signature ((polyRelation-p) op-p)))
  (case-match term
    ((op & &) (op-fix op))
    (& '<)))

(def::signature relation-op (t) op-p)

(def::un polyRelation (op var p2)
  (declare (xargs :signature ((t t t) polyRelation-p)))
  `(,(op-fix op) ,(bound-poly-fix var) ,(poly-fix! p2)))

(defthm relation-op-polyRelation
  (equal (relation-op (polyRelation op var p2))
         (op-fix op)))

(defthm relation-bounding-poly-polyRelation
  (equal (relation-bounding-poly (polyRelation op var p2))
         (poly-fix p2)))

(defthm relation-bound-poly-polyRelation
  (equal (relation-bound-poly (polyRelation op var p2))
         (bound-poly-fix var)))

(in-theory (disable polyRelation polyRelation-p))
(in-theory (disable relation-op relation-bound-poly relation-bounding-poly))

(def::und polyRelation-witness ()
  (declare (xargs :signature (() polyRelation-p)))
  (polyRelation (op-witness) (varid-witness) (poly-witness)))

(in-theory (disable (polyRelation-witness)))

;; ==========================================

(def::type+ polyGreater-p (term)
  (declare (xargs :type-name polyGreater
                  :type-witness (polyRelation '> (varid-witness) (poly-witness))))
  (and (polyRelation-p term)
       (gt-op-p (relation-op term))))

(fty::deffixtype polyGreater
  :pred   polyGreater-p
  :fix    polyGreater-fix
  :equiv  polyGreater-equiv
  :define nil
  )

(def::type+ variableGreater-p (term)
  (declare (xargs :type-name variableGreater
                  :type-witness (polyRelation '> (varid-witness) (poly-witness))))
  (and (polyGreater-p term)
       (varid-p (relation-bound-poly term))))

(fty::deffixtype variableGreater
  :pred   variableGreater-p
  :fix    variableGreater-fix
  :equiv  variableGreater-equiv
  :define nil
  )

(def::signature polyRelation (gt-op-p varid-p t) variableGreater-p)

;; ==========================================

(def::type+ polyLess-p (term)
  (declare (xargs :type-name polyLess
                  :type-witness (polyRelation '< (varid-witness) (poly-witness))))
  (and (polyRelation-p term)
       (lt-op-p (relation-op term))))

(fty::deffixtype polyLess
  :pred   polyLess-p
  :fix    polyLess-fix
  :equiv  polyLess-equiv
  :define nil
  )

(def::type+ variableLess-p (term)
  (declare (xargs :type-name variableLess
                  :type-witness (polyRelation '< (varid-witness) (poly-witness))))
  (and (polyLess-p term)
       (varid-p (relation-bound-poly term))))

(fty::deffixtype variableLess
  :pred   variableLess-p
  :fix    variableLess-fix
  :equiv  variableLess-equiv
  :define nil
  )

(def::signature polyRelation (lt-op-p varid-p t) variableLess-p)

(defthm less-is-not-greater
  (implies
   (variableLess-p x)
   (not (variableGreater-p x)))
  :rule-classes (:forward-chaining))

(defthm greater-is-not-less
  (implies
   (variableGreater-p x)
   (not (variableLess-p x)))
  :rule-classes (:forward-chaining))

;; ==========================================

(def::type+ variableInequality-p (term)
  (declare (xargs :type-name variableInequality
                  :type-witness (variableGreater-witness)))
  (or (variableGreater-p term)
      (variableLess-p term)))

(defthm variableInequality-p-implies
  (implies
   (variableInequality-p term)
   (and (polyRelation-p term)
        (varid-p (relation-bound-poly term))
        (ineq-op-p (relation-op term))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable variableInequality-p))))

(defthm implies-variableInequality-p
  (implies
   (and (polyRelation-p term)
        (varid-p (relation-bound-poly term))
        (ineq-op-p (relation-op term)))
   (variableInequality-p term))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable variableInequality-p))))

(fty::deffixtype variableInequality
  :pred   variableInequality-p
  :fix    variableInequality-fix
  :equiv  variableInequality-equiv
  :define nil
  )

;; ==========================================

(def::type+ variableEquality-p (term)
  (declare (xargs :type-name variableEquality
                  :type-witness (polyRelation '= (varid-witness) (poly-witness))))
  (and (polyRelation-p term)
       (varid-p (relation-bound-poly term))
       (eq-op-p (relation-op term))))

(fty::deffixtype variableEquality
  :pred   variableEquality-p
  :fix    variableEquality-fix
  :equiv  variableEquality-equiv
  :define nil
  )

(defthm variableEquality-not-variableInequality
  (implies
   (variableEquality-p term)
   (not (variableInequality-p term)))
  :hints (("Goal" :in-theory (disable BODY-IMPLIES-EQ-OP-P)))
  :rule-classes (:forward-chaining))

(defthm variableInequality-not-variableEquality
  (implies
   (variableInequality-p term)
   (not (variableEquality-p term)))
  :rule-classes (:forward-chaining))

;; ==========================================

(def::type+ variableRelation-p (term)
  (declare (xargs :type-name variableRelation
                  :type-witness (variableEquality-witness)))
  (or (variableInequality-p term)
      (variableEquality-p term)))

(fty::deffixtype variableRelation
  :pred   variableRelation-p
  :fix    variableRelation-fix
  :equiv  variableRelation-equiv
  :define nil
  )

(defthm variableRelation-p-implies
  (implies
   (variableRelation-p term)
   (and (polyRelation-p term)
        (varid-p (relation-bound-poly term))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable variableRelation-p))))

(defthm implies-variableRelation-p
  (implies
   (and (polyRelation-p term)
        (varid-p (relation-bound-poly term)))
   (variableRelation-p term))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable variableRelation-p))))

;; ==========================================

(def::un variableRelation (op var poly)
  (declare (xargs :signature ((t t t) variableRelation-p)))
  (polyRelation op (varid-fix var) poly))

(defthm relation-bounding-poly-variablerelation
  (equal (relation-bounding-poly (variableRelation op var poly))
         (poly-fix poly))
  :hints (("Goal" :in-theory (enable relation-bounding-poly))))

(defthm relation-op-variablerelation
  (equal (relation-op (variableRelation op var poly))
         (op-fix op))
  :hints (("Goal" :in-theory (enable relation-op))))

(defthm relation-bound-poly-variablerelation
  (equal (relation-bound-poly (variableRelation op var poly))
         (varid-fix var))
  :hints (("Goal" :in-theory (enable relation-bound-poly))))

(def::signature variableRelation (lt-op-p t t) variableLess-p)
(def::signature variableRelation (eq-op-p t t) variableEquality-p)

(def::signature relation-op (variableGreater-p)    gt-op-p)
(def::signature relation-op (variableLess-p)       lt-op-p)
(def::signature relation-op (variableEquality-p)   eq-op-p)
(def::signature relation-op (variableInequality-p) ineq-op-p)

(def::un variableLess (var relation poly)
  (declare (xargs :signature ((varid-p relation-p poly-p) variableLess-p)))
  (variableRelation (relative-op (fix-relation relation) '<) var poly))

(def::signature variableLess (t t t) variableLess-p)

(def::un variableGreater (var relation poly)
  (declare (xargs :signature ((varid-p relation-p poly-p) variableGreater-p)))
  (variableRelation (relative-op (fix-relation relation) '>) var poly))

(def::signature variableGreater (t t t) variableGreater-p)

(def::un variableEquality (var poly)
  (declare (xargs :signature ((varid-p poly-p) variableEquality-p)))
  (variableRelation '= var poly))

(def::signature variableEquality (t t) variableEquality-p)

;; ==========================================

(defun polyInterval-p (term)
  (declare (type t term))
  (case-match term
    (('and gt lt) (and (polyGreater-p gt)
                       (polyLess-p lt)))
    (& nil)))

(defthm polyInterval-not-polyRelation
  (implies
   (polyInterval-p term)
   (not (polyRelation-p term)))
  :hints (("Goal" :in-theory (enable polyRelation-p)))
  :rule-classes (:forward-chaining))

(defthm polyRelation-not-polyInterval
  (implies
   (polyRelation-p term)
   (not (polyInterval-p term)))
  :hints (("Goal" :in-theory (enable polyRelation-p)))
  :rule-classes (:forward-chaining))

(def::un interval-lt (term)
  (declare (xargs :signature ((polyInterval-p) polyLess-p)))
  (case-match term
    (('and & lt) (polyLess-fix lt))
    (& (variableLess-witness))))

(def::signature interval-lt (t) polyLess-p)

(def::un interval-gt (term)
  (declare (xargs :signature ((polyInterval-p) polyGreater-p)))
  (case-match term
    (('and gt &) (polyGreater-fix gt))
    (& (variableGreater-witness))))

(def::signature interval-gt (t) polyGreater-p)

(def::un polyInterval (gt lt)
  (declare (xargs :signature ((t t) polyInterval-p)))
  (let ((gt     (polyGreater-fix gt))
        (lt     (polyLess-fix lt)))
    `(and ,gt ,lt)))

(defthm interval-gt-polyInterval
  (equal (interval-gt (polyInterval gt lt))
         (polyGreater-fix gt)))

(defthm interval-lt-polyInterval
  (equal (interval-lt (polyInterval gt lt))
         (polyLess-fix lt)))

(in-theory (disable polyInterval polyInterval-p))
(in-theory (disable interval-lt interval-gt))

;; ==========================================

(def::type+ variableInterval-p (term)
  (declare (xargs :type-name variableInterval
                  :type-witness (polyInterval (variableGreater-witness) (variableLess-witness))))
  (and (polyInterval-p term)
       (variableGreater-p (interval-gt term))
       (variableLess-p (interval-lt term))))

(fty::deffixtype variableInterval
  :pred   variableInterval-p
  :fix    variableInterval-fix
  :equiv  variableInterval-equiv
  :define nil
  )

(defthm variableInterval-not-variableRelation
  (implies
   (variableInterval-p term)
   (not (variableRelation-p term)))
  :rule-classes (:forward-chaining))

(defthm variableRelation-not-variableInterval
  (implies
   (variableRelation-p term)
   (not (variableInterval-p term)))
  :rule-classes (:forward-chaining))

(def::un variableInterval (gt lt)
  (declare (xargs :signature ((t t) variableInterval-p)
                  :guard (and (variableGreater-p gt)
                              (variableLess-p lt))))
  (polyInterval (variableGreater-fix gt)
                (variableLess-fix lt)))

(defthm interval-gt-variableInterval
  (equal (interval-gt (variableInterval gt lt))
         (variableGreater-fix gt)))

(defthm interval-lt-variableInterval
  (equal (interval-lt (variableInterval gt lt))
         (variableLess-fix lt)))

(in-theory (disable variableInterval))

;; ============================

(def::type+ polyBound-p (term)
  (declare (xargs :type-name polyBound
                  :type-witness (polyRelation-witness)))
  (or (polyInterval-p term)
      (polyRelation-p term)))

(def::type+ variableBound-p (term)
  (declare (xargs :type-name variableBound
                  :type-witness (variableRelation-witness)))
  (or (variableInterval-p term)
      (variableRelation-p term)))

(defthm variableBound-implies-polyBound
  (implies
   (variableBound-p term)
   (polyBound-p term))
  :rule-classes (:forward-chaining))

;; ============================

(def::un bound-bound-poly (term)
  (declare (xargs :signature ((polyBound-p) bound-poly-p)))
  (if (polyInterval-p term)
      (relation-bound-poly (interval-gt term))
    (relation-bound-poly term)))

(def::un bound-varid (term)
  (declare (xargs :signature ((variableBound-p) varid-p)))
  (varid-fix (bound-bound-poly term)))

(def::signature bound-varid (t) varid-p)

(defthm
  bound-varid-variablerelation
  (equal (bound-varid (variablerelation op var poly))
         (varid-fix var))
  :hints (("goal" :in-theory (e/d (relation-bound-poly bound-varid)
                                  ((:definition relation-bound-poly))))))

(defthmd bound-varid-to-relation-bound-poly
  (implies
   (variableRelation-p term)
   (equal (bound-varid term)
          (relation-bound-poly term))))

(in-theory (disable bound-varid bound-bound-poly))

(def::signature append (varid-listp varid-listp) varid-listp
  :hints (("Goal" :in-theory (enable append))))

(def::un bounding-variables (term)
  (declare (xargs :signature ((variableBound-p) varid-listp)))
  (if (variableInterval-p term)
      (append (get-poly-variables (relation-bounding-poly (interval-gt term)))
              (get-poly-variables (relation-bounding-poly (interval-lt term))))
    (get-poly-variables (relation-bounding-poly term))))

(defthm open-bounding-variables
  (implies
   (variableInterval-p term)
   (equal (bounding-variables term)
          (append (bounding-variables (interval-gt term))
                  (bounding-variables (interval-lt term)))))
  :hints (("Goal" :in-theory (disable VARIABLEINTERVAL-P))))

(def::signature bounding-variables (t) varid-listp)

;; Mihir M. mod Nov. 2020: I added the following 4 helper lemmas.
(defthm bounding-variables-variablerelation-lemma-1
  (consp (cdr (polyrelation op (varid-fix varid)
                            poly)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable polyrelation)))
  :rule-classes :type-prescription)

(defthm bounding-variables-variablerelation-lemma-2
  (consp (cddr (polyrelation op (varid-fix varid)
                             poly)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable polyrelation)))
  :rule-classes :type-prescription)

(defthm bounding-variables-variablerelation-lemma-3
  (equal
   (pair-list-nz-keys (poly->coeff (caddr (polyrelation op (varid-fix varid)
                                                        poly))))
   (pair-list-nz-keys (poly->coeff poly)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable polyrelation))))

(defthm bounding-variables-variablerelation-lemma-4
  (equal (cdddr (polyrelation op (varid-fix varid)
                              poly))
         nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable polyrelation)))
  :rule-classes :type-prescription)

(defthm bounding-variables-variablerelation
  (equal (bounding-variables (variablerelation op varid poly))
         (get-poly-variables poly))
  :hints (("Goal" :in-theory (enable get-poly-variables relation-bounding-poly))))

(defthm abstract-get-poly-variables-relation-bounding-poly
  (implies
   (variableRelation-p term)
   (equal (get-poly-variables (relation-bounding-poly term))
          (bounding-variables term))))

(in-theory (disable bounding-variables))

(defun normalized-variableInterval-p (x)
  (declare (type t x))
  (if (variableInterval-p x)
      (equal (bound-varid (interval-gt x))
             (bound-varid (interval-lt x)))
    t))

(defthm normalized-variableInterval-from-variableRelation-p
  (implies
   (variableRelation-p x)
   (normalized-variableInterval-p x)))

(defthm normalized-variableInterval-implication
  (implies
   (and
    (normalized-variableInterval-p x)
    (variableInterval-p x))
   (and (equal (bound-varid (interval-gt x))
               (bound-varid x))
        (equal (bound-varid (interval-lt x))
               (bound-varid x))))
  :hints (("Goal" :in-theory (e/d (bound-varid bound-bound-poly) (variableInterval-p)))))

(in-theory (disable normalized-variableInterval-p))

(defun normalized-variableBound-p (term)
  (declare (type t term))
  (and (variableBound-p term)
       (>-all (bound-varid term) (bounding-variables term))
       (normalized-variableInterval-p term)))

(defthm normalized-variableBound-p-implication
  (implies
   (normalized-variableBound-p term)
   (and (variableBound-p term)
        (>-all (bound-varid term) (bounding-variables term))
        (normalized-variableInterval-p term)))
  :rule-classes (:forward-chaining))

(defthm normalized-variableBound-gt-lt
  (implies
   (and
    (normalized-variableBound-p x)
    (variableInterval-p x))
   (and (normalized-variableBound-p (interval-gt x))
        (normalized-variableBound-p (interval-lt x)))))

(defthm normalized-variableBound-p-variableRelation
  (implies
   (force (>-all varid (get-poly-variables poly)))
   (normalized-variableBound-p (variableRelation op varid poly)))
  :hints (("Goal" :in-theory (e/d nil (variableRelation ADVISER::>-ALL-BY-MULTIPLICITY)))))

(defthm bound-varid-variableinterval
  (equal (bound-varid (variableinterval x y))
         (bound-varid (variableGreater-fix x)))
  :hints (("Goal" :in-theory (e/d (bound-varid bound-bound-poly) (variableinterval VARIABLEINTERVAL-P)))))

(defthm normalized-variableInterval-p-variableinterval
  (implies
   (force
    (and
     (equal (bound-varid x) (bound-varid y))
     (variablegreater-p x)
     (variableless-p y)))
   (normalized-variableInterval-p (variableinterval x y)))
  :hints (("Goal" :in-theory (e/d (NORMALIZED-VARIABLEINTERVAL-P)
                                  (variableinterval VARIABLEINTERVAL-P)))))

(defthm normalized-variableBound-p-variableinterval
  (implies
   (force
    (and
     (equal (bound-varid x) (bound-varid y))
     (variablegreater-p x)
     (variableless-p y)
     (normalized-variableBound-p x)
     (normalized-variableBound-p y)))
   (normalized-variableBound-p (variableinterval x y)))
  :hints (("Goal" :in-theory (e/d nil
                                  (variablegreater-p
                                   variableless-p
                                   VARIABLEBOUND-P
                                   VARIABLERELATION-P
                                   VARIABLEINTERVAL-P
                                   variableinterval ADVISER::>-ALL-BY-MULTIPLICITY)))))

(in-theory (disable normalized-variableBound-p))

(in-theory (disable variableRelation relation-op))
(in-theory (disable variableRelation-p variableEquality-p variableInequality-p variableGreater-p variableLess-p))
(in-theory (disable variableInterval interval-lt interval-gt))
(in-theory (disable variableInterval-p))
(in-theory (disable variableBound-p))

(defthm eval-ineq-polyRelationp
  (implies
   (polyRelation-p term)
   (equal (eval-ineq term env)
          (let ((op (relation-op term)))
            (if (equal (op-relation op) :inclusive)
                (cond
                 ((lt-op-p op)
                  (<= (eval-poly (bound-poly (bound-bound-poly term)) env)
                      (eval-poly (relation-bounding-poly term) env)))
                 ((gt-op-p op)
                  (>= (eval-poly (bound-poly (bound-bound-poly term)) env)
                      (eval-poly (relation-bounding-poly term) env)))
                 (t
                  (equal (eval-poly (bound-poly (bound-bound-poly term)) env)
                         (eval-poly (relation-bounding-poly term) env))))
              (cond
               ((lt-op-p op)
                (<  (eval-poly (bound-poly (bound-bound-poly term)) env)
                    (eval-poly (relation-bounding-poly term) env)))
               (t
                (> (eval-poly (bound-poly (bound-bound-poly term)) env)
                   (eval-poly (relation-bounding-poly term) env))))))))
  :hints (("Goal" :do-not '(preprocess)
           ;;:in-theory (enable bound-varid-to-relation-bound-poly)
           ;;:do-not-induct t)
           ;;(and stable-under-simplificationp
           ;;'(
           :in-theory (enable eval-ineq relation-op relation-bound-poly relation-bounding-poly variableRelation-p
                              polyGreater-p polyLess-p bound-bound-poly bound-poly-fix bound-poly-p polyRelation-p
                              polyInterval-p
                              variableEquality-p variableInequality-p variableLess-p variableGreater-p))))

(defthm bound-poly-to-varid
  (implies
   (variableRelation-p term)
   (equal (eval-poly (bound-poly (bound-bound-poly term)) env)
          (rfix (binding->value (get-binding (bound-varid term) env)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable bound-varid bound-bound-poly VARIABLERELATION-P))))

(defthm eval-ineq-polyIntervalp
  (implies
   (polyInterval-p term)
   (equal (eval-ineq term env)
          (and (eval-ineq (interval-gt term) env)
               (eval-ineq (interval-lt term) env))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable eval-ineq interval-gt interval-lt polyInterval-p variableInterval-p))))

(in-theory (disable relation-p signum))

(defthm similarinequalities-variableless
  (implies
   (and
    (variableless-p x)
    (variableless-p y))
   (similarinequalities (relation-op x)
                        (relation-op y)))
  :hints (("goal" :in-theory (enable similarinequalities)))
  :rule-classes (:type-prescription))

(defthm similarinequalities-variablegreater
  (implies
   (and
    (variablegreater-p x)
    (variablegreater-p y))
   (similarinequalities (relation-op x)
                        (relation-op y)))
  :hints (("goal" :in-theory (enable similarinequalities)))
  :rule-classes (:type-prescription))

(defun variableBound-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (variableBound-p (car list))
         (variableBound-listp (cdr list)))))

(defthm true-listp-variableBound-listp
  (implies
   (variableBound-listp list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(defthm variableBound-listp-append
  (implies
   (and
    (variableBound-listp x)
    (variableBound-listp y))
   (variableBound-listp (append x y))))

(defun conjoinResults (x list)
  (declare (type t x list))
  (if (not (consp list)) x
    `(and ,x ,(conjoinResults (car list) (cdr list)))))

(defthm eval-ineq-and
  (equal (eval-ineq (cons 'and (cons x (cons y nil))) env)
         (and (eval-ineq x env)
              (eval-ineq y env)))
  :hints (("Goal" :in-theory (enable eval-ineq))))


(in-theory (enable signum))

(def::un compareTo (x y)
  (declare (xargs :signature ((rationalp rationalp) tri-p)))
  (signum (- x y)))

(in-theory (enable gt-op-p lt-op-p))

(defthm variablegreater-from-variableinequality
  (implies
   (and
    (variableinequality-p x)
    (gt-op-p (relation-op x)))
   (variablegreater-p x)))

(defthm variableless-from-variableinequality
  (implies
   (and
    (variableinequality-p x)
    (lt-op-p (relation-op x)))
   (variableless-p x)))

(defthmd destructure-conjoinresults-helper-1
  (equal (eval-ineq (conjoinresults z (append x y)) cex)
         (and (eval-ineq (conjoinresults z x) cex)
              (eval-ineq (conjoinresults z y) cex))))

(def::un bound-append (x y)
  (declare (xargs :signature ((variableBound-listp variableBound-listp) variableBound-listp)))
  (append x y))

(defthm destructure-conjoinresults
  (implies
   (and
    (force (variableGreater-p gt))
    (force (variableLess-p lt)))
   (equal (eval-ineq (conjoinresults (variableinterval gt lt)
                                     (bound-append gtres ltres)) cex)
          (and (eval-ineq (conjoinresults gt gtres) cex)
               (eval-ineq (conjoinresults lt ltres) cex))))
  :hints (("Goal" :in-theory (e/d (variableinterval destructure-conjoinresults-helper-1)
                                  (EVAL-INEQ-polyRELATIONP))
           :expand ((:free (lt) (conjoinresults lt ltres))
                    (:free (gt) (conjoinresults gt gtres)))
           :do-not-induct t)))

(in-theory (disable bound-append))

(defun normalized-variableBound-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (normalized-variableBound-p (car list))
         (normalized-variableBound-listp (cdr list)))))

(defthm normalized-variableBound-listp-append
  (implies
   (force
    (and
     (normalized-variableBound-listp x)
     (normalized-variableBound-listp y)))
   (normalized-variableBound-listp (append x y))))

(defthm normalized-variableBound-listp-bound-append
  (implies
   (force
    (and
     (normalized-variableBound-listp x)
     (normalized-variableBound-listp y)))
   (normalized-variableBound-listp (bound-append x y)))
  :hints (("Goal" :in-theory (enable bound-append))))

(defun variableBound-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (variableBound-p (car list))
         (variableBound-listp (cdr list)))))

(defthm normalized-variableBound-listp-implies-variableBound-listp
  (implies
   (normalized-variableBound-listp list)
   (variableBound-listp list))
  :rule-classes (:rewrite :forward-chaining))

(def::un bound-varid-list (list)
  (declare (xargs :signature ((variableBound-listp) varid-listp)))
  (if (not (consp list)) nil
    (let ((bound (car list)))
      (cons (bound-varid bound)
            (bound-varid-list (cdr list))))))

(defthm bound-varid-list-bound-append
  (equal (bound-varid-list (bound-append x y))
         (append (bound-varid-list x)
                 (bound-varid-list y)))
  :hints (("Goal" :in-theory (enable bound-append))))

(defthm bound-varid-list-append
  (equal (bound-varid-list (append x y))
         (append (bound-varid-list x)
                 (bound-varid-list y))))

(def::un all-bound-variables (term)
  (declare (xargs :signature ((variableBound-p) varid-listp)))
  (cons (bound-varid term)
        (bounding-variables term)))

(def::un all-bound-list-variables (list)
  (declare (xargs :signature ((variableBound-listp) varid-listp)))
  (if (not (consp list)) nil
    (append (all-bound-variables (car list))
            (all-bound-list-variables (cdr list)))))

(defthm bound-varid-list-in-all-bound-list-variables
  (implies
   (list::memberp a (bound-varid-list list))
   (list::memberp a (all-bound-list-variables list))))

(defthm subset-p-bound-varid-list-all-bound-list-variables
  (subset-p (bound-varid-list list) (all-bound-list-variables list)))

(defthm set-upper-bound-equiv-bound-varid-list
  (set-upper-bound-equiv (bound-varid-list list)
                         (all-bound-list-variables list)))

(defthm all-bound-list-variables-bound-append
  (equal (all-bound-list-variables (bound-append x y))
         (append (all-bound-list-variables x)
                 (all-bound-list-variables y)))
  :hints (("Goal" :in-theory (enable bound-append))))

(defthm all-bound-list-variables-append
  (equal (all-bound-list-variables (append x y))
         (append (all-bound-list-variables x)
                 (all-bound-list-variables y)))
  :hints (("Goal" :in-theory (enable bound-append))))

(defun trapezoid-p (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (let ((bv (car list)))
      (and (normalized-variableBound-p bv)
           (variableBound-listp (cdr list))
           (>-all (bound-varid bv) (all-bound-list-variables (cdr list)))
           (trapezoid-p (cdr list))))))

(defthm trapezoid-implication
  (implies
   (trapezoid-p list)
   (normalized-variableBound-listp list))
  :rule-classes :forward-chaining)

(def::un eval-zoid (list env)
  (declare (xargs :signature ((t t) booleanp)))
  (let ((env (env-fix-type! env)))
    (if (not (consp list)) t
      (let ((entry (car list)))
        (and (eval-ineq entry env)
             (eval-zoid (cdr list) env))))))

(defthm consp-set-subtract
  (iff (consp (set-subtract x y))
       (not (subset-p x y)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (consp-is-not-empty-p) (empty-p))
           :restrict ((consp-is-not-empty-p ((x (set-subtract x y))))))
          (quant::inst?)))

(defthm broken-abstraction-rule
  (implies
   (and
    (normalized-variablebound-p x)
    (normalized-variablebound-p y)
    (not-constp (sub (relation-bounding-poly y) (relation-bounding-poly x)))
    (variableRelation-p x)
    (variableRelation-p y))
   (list::memberp (leading-variable (sub (relation-bounding-poly y)
                                         (relation-bounding-poly x)))
                  (APPEND (GET-POLY-VARIABLES (RELATION-BOUNDING-POLY Y))
                          (GET-POLY-VARIABLES (RELATION-BOUNDING-POLY X)))))
  :hints (("Goal" :in-theory (e/d (leading-variable-is-in-bounding-variables-when-not-constp
                                   not-constp-definition bounding-variables leading-variable-definition)
                                  (SUBSET-P-BY-MULTIPLICITY abstract-get-poly-variables-relation-bounding-poly))
           :use (:instance leading-variable-is-in-bounding-variables-when-not-constp
                           (poly (sub (relation-bounding-poly y) (relation-bounding-poly x)))))))

(defthm memberp-upper-bound-leading-variable-sub
  (implies
   (and
    (normalized-variablebound-p x)
    (normalized-variablebound-p y)
    (not-constp (sub (relation-bounding-poly y) (relation-bounding-poly x)))
    (variableRelation-p x)
    (variableRelation-p y))
   (memberp-upper-bound-equiv (leading-variable (sub (relation-bounding-poly y)
                                                     (relation-bounding-poly x)))
                              (APPEND (GET-POLY-VARIABLES (RELATION-BOUNDING-POLY Y))
                                      (GET-POLY-VARIABLES (RELATION-BOUNDING-POLY X)))))
  :hints (("Goal" :in-theory '(MEMBERP-UPPER-BOUND-CTX MEMBERP-UPPER-BOUND-PRED)
           :use broken-abstraction-rule)
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))))
