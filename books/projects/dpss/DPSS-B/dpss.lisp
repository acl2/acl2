;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "util")
(include-book "binder")
(include-book "coi/util/good-rewrite-order" :dir :system)

(encapsulate
    ()

  (local (in-theory (enable ifix)))

  (def::type sign (x)
    :body (or (equal x 1) (equal x -1))
    :refines (int)
    :type-witness 1
    :forward-chain-or t
    )

  )
  
(defthm sign-p-negation
  (implies
   (sign-p x)
   (sign-p (- x)))
  :hints (("Goal" :in-theory (enable sign-p))))

(def::und snot (x)
  (declare (xargs :signature ((sign-p) sign-p)))
  (- x))

(def::type-str UAV
  ((LP rational)
   (LC nat)
   (xx rational)
   (dx sign)
   (RC nat)
   (RP rational)))

(defthm dx-is-not-zero
  (not (equal (UAV->dx uav) 0))
  :rule-classes ((:forward-chaining :trigger-terms ((UAV->dx uav)))))

(defmacro UAV* (uav &key (LP 'nil) (LC 'nil) (xx 'nil) (dx 'nil) (RC 'nil) (RP 'nil))
  `(let ((LP ,(or LP `(UAV->LP ,uav)))
         (LC ,(or LC `(UAV->LC ,uav)))
         (xx ,(or xx `(UAV->xx ,uav)))
         (dx ,(or dx `(UAV->dx ,uav)))
         (RC ,(or RC `(UAV->RC ,uav)))
         (RP ,(or RP `(UAV->RP ,uav))))
     (UAV LP LC xx dx RC RP)))

(defmacro UAV! (&key (LP 'nil LP-p) (LC 'nil LC-p) (xx 'nil xx-p) (dx 'nil dx-p) (RC 'nil RC-p) (RP 'nil RP-p))
  (declare (xargs :guard (and LP-p LC-p xx-p dx-p RC-p RP-p))
           (ignorable LP-p LC-p xx-p dx-p RC-p RP-p))
  `(UAV* nil :LP ,LP :LC ,LC :xx ,xx :dx ,dx :RC ,RC :RP ,RP))

(def-b*-binder UAV*
  :body (patbind-fn args '((LP . UAV->LP)
                           (LC . UAV->LC)
                           (xx . UAV->xx)
                           (dx . UAV->dx)
                           (RC . UAV->RC)
                           (RP . UAV->RP))
                    forms rest-expr))

(def::un seg-size-fn2 (n d)
  (declare (xargs :fty ((int rational) prat)))
  (/ (/ (pos-fix n) (prat-fix d))))

(in-theory (disable seg-size-fn2))

(def::un seg-size-fn (LP L S R RP)
  (declare (xargs :fty ((rational int nat int rational) prat)))
  (seg-size-fn2 (+ L R S) (- RP LP)))
  
(def::und UAV->seg-size (uav)
  (declare (xargs :fty ((uav) prat)))
  (b* (((UAV* :LP LP :LC LC :RC RC :RP RP) uav))
    (seg-size-fn LP LC 1 RC RP)))

(def::un left-moving-uav-split-offset-fn (x ss)
  (declare (xargs :fty ((int rational) rational)))
  (* x ss))

(def::un right-moving-uav-split-offset-fn (x ss)
  (declare (xargs :fty ((int rational) rational)))
  (+ (left-moving-uav-split-offset-fn x ss) ss))

(def::und UAV->left-moving-uav-split-location (uav)
  (declare (xargs :fty ((uav) rational)))
  (b* (((UAV* :LP LP :LC LC) uav))
    (+ LP (left-moving-uav-split-offset-fn LC (UAV->seg-size uav)))))

(def::und UAV->right-moving-uav-split-location (uav)
  (declare (xargs :fty ((uav) rational)))
  (b* (((UAV* :LP LP :LC LC) uav))
    (+ LP (right-moving-uav-split-offset-fn LC (UAV->seg-size uav)))))

(defthm uav-split-location-ordering
  (< (UAV->left-moving-uav-split-location uav)
     (UAV->right-moving-uav-split-location uav))
  :hints (("Goal" :in-theory (enable UAV->right-moving-uav-split-location
                                     UAV->left-moving-uav-split-location)))
  :rule-classes (:linear))

;;
;; Equivalences
;;

;;
;; end-equiv
;;

(defun end (x)
  (declare (type t x))
  (if (consp x) (end (cdr x)) x))

(defun end-equiv (x y)
  (declare (type t x y))
  (equal (end x) (end y)))

;; (defthm end-equiv-cons-x
;;   (equal (end-equiv (cons a x) y)
;;          (end-equiv x y)))

;; (defthm end-equiv-cons-y
;;   (equal (end-equiv x (cons a y))
;;          (end-equiv x y)))

(defthm end-equiv-base
  (implies
   (and (not (consp x)) (not (consp y)))
   (equal (end-equiv x y)
          (equal x y))))

(defequiv end-equiv)

(defcong end-equiv equal (end x) 1)

(defthm end-equiv-cons
  (end-equiv (cons a x) x))

(defthm end-equiv-append
  (end-equiv (append x y) y))

(in-theory (disable end-equiv))

(encapsulate
    ()

  (local
   (defthm end-equiv-update-nth-1
     (implies
      (< (nfix n) (len x))
      (end-equiv (update-nth n v x) x))))

  (local
   (defthm end-equiv-update-nth-2
     (implies
      (<= (len x) (nfix n))
      (end-equiv (update-nth n v x) nil))))

  (defthm end-equiv-update-nth
    (end-equiv (update-nth n v x)
               (if (< (nfix n) (len x)) x nil)))

  )

(defthm true-listp-implies-end-equiv-nil
  (implies
   (true-listp x)
   (end-equiv x nil))
  :rule-classes (:forward-chaining))

(defcong end-equiv equal (true-listp x) 1)

(defthmd end-equiv-nil-implies-true-listp
  (implies
   (end-equiv x nil)
   (true-listp x)))

(defthmd end-equiv-nil-is-true-listp
  (iff (end-equiv x nil)
       (true-listp x)))

(defthm not-consp-implies-list-equiv-nil
  (implies
   (not (consp x))
   (list-equiv x nil))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable true-list-fix list-equiv))))

;;
;; len-equiv
;;

(defthm zero-len-implies-not-consp
  (implies
   (equal (len ens) 0)
   (not (consp ens)))
  :rule-classes (:forward-chaining))

(defun len-equiv (x y)
  (declare (xargs :guard t))
  (equal (len (list-fix x))
         (len (list-fix y))))

(defequiv len-equiv)

(defrefinement list-equiv len-equiv)

(defcong len-equiv equal (len x) 1)

(defcong len-equiv equal (consp x) 1)

(defthm consp-len
  (implies
   (consp x)
   (<= 1 (len x)))
  :rule-classes (:linear))

(defthm not-consp-implies-len-equiv-nil
  (implies
   (not (consp x))
   (len-equiv x 0))
  :rule-classes (:forward-chaining))

(in-theory (disable len-equiv))

(defun-sk nth-equiv (x y)
  (declare (xargs :guard t))
  (forall (i) (equal (nth (nfix i) (list-fix x))
                     (nth (nfix i) (list-fix y)))))

(defthmd nth-equiv-implication
  (implies
   (nth-equiv x y)
   (equal (nth i x)
          (nth i y)))
  :hints (("Goal" :use nth-equiv-necc))
  :rule-classes ((:rewrite :loop-stopper ((x y)))))

(in-theory (disable nth-equiv))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (in-theory (enable nth-equiv-implication))

     (defthm nth-equiv-id
       (nth-equiv x x)
       :hints (("Goal" :expand (nth-equiv x x))))
     
     (defthm nth-equiv-commutes
       (IMPLIES
        (NTH-EQUIV X Y)
        (NTH-EQUIV Y X))
       :hints (("Goal" :expand (NTH-EQUIV Y X))))
     
     (defthm nth-equiv-transitive
       (IMPLIES
        (AND (NTH-EQUIV X Y)
             (NTH-EQUIV Y Z))
        (NTH-EQUIV X Z))
       :hints (("Goal" :expand (NTH-EQUIV X Z))))

     ))
     
  (defequiv nth-equiv)

  )

(defrefinement list-equiv nth-equiv
  :hints (("Goal" :in-theory (enable nth-equiv))))

(defcong nth-equiv equal (nth i x) 2
  :hints (("Goal" :use (:instance nth-equiv-implication
                                  (x x)
                                  (y X-EQUIV)))))

(defthm zp-implies-zero-nth-equiv
  (implies
   (zp x)
   (nat-equiv x 0))
  :hints (("Goal" :in-theory (enable nat-equiv)))
  :rule-classes (:forward-chaining))

(defthm nth-nil
  (equal (nth x nil) nil)
  :hints (("Goal" :expand (nth x nil))))
  
(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (local
      (encapsulate
          ()

        (in-theory (disable zp-open NTH-EQUIV-IMPLIES-EQUAL-NTH-2))
        (IN-THEORY (ENABLE QUANT::OPEN-NTH))
        
        (defthm nth-plus
          (equal (nth (+ 1 (nfix x)) y)
                 (nth x (cdr y)))
          :hints (("Goal" :expand (nth (+ 1 (nfix x)) y))))
        
        ))
     
     (defthmd nth-equiv-cons
       (iff (nth-equiv (cons a x) y)
            (if (not (consp y)) (and (null a) (nth-equiv x nil))
              (and (equal a (nth 0 y))
                   (nth-equiv x (cdr y)))))
       :hints ((pattern-hint
                (NTH-EQUIV (CONS A X) Y)
                :use ((:instance NTH-EQUIV-IMPLICATION
                                 (x (CONS A X))
                                 (y y)
                                 (i (+ 1 (nfix (NTH-EQUIV-WITNESS X (CDR Y))))))
                      (:instance NTH-EQUIV-IMPLICATION
                                 (x (CONS A X))
                                 (y y)
                                 (i 0)))
                :expand ((NTH-EQUIV X (CDR Y))))
               (pattern-hint
                (not (nth-equiv (cons a x) y))
                :expand ((nth-equiv (cons a x) y)))
               (pattern-hint
                (:and
                 (NTH-EQUIV X NIL)
                 (nth i x))
                :use (:instance NTH-EQUIV-IMPLICATION
                                (x x)
                                (y 'nil)
                                (i i)))
               (and stable-under-simplificationp
                    '(:in-theory (enable NTH-EQUIV-IMPLIES-EQUAL-NTH-2)))
               
               ))))
  
  (local
   (defthm len-equiv-cons
     (iff (len-equiv (cons a x) y)
          (and (consp y)
               (len-equiv x (cdr y))))
     :hints (("Goal" :in-theory (enable len-equiv)))))

  (local
   (encapsulate
       ()
     
     (defun equal-list (x y)
       (if (and (consp x) (consp y))
           (and (equal (car x) (car y))
                (equal-list (cdr x) (cdr y)))
         (and (not (consp x))
              (not (consp y))
              (equal x y))))
     
     (defthmd equal-to-equal-list
       (iff (equal x y)
            (equal-list x y)))
     
     (defthm equal-list-to-nth-equiv-reduction
       (iff (equal-list x y)
            (and (len-equiv x y)
                 (nth-equiv x y)
                 (end-equiv x y)))
       :hints (("Goal" :in-theory (enable nth-equiv-cons)
                :induct (equal-list x y))))
     
     ))
     
  (defthmd equal-to-nth-equiv-reduction
    (iff (equal x y)
         (and (len-equiv x y)
              (nth-equiv x y)
              (end-equiv x y)))
    :hints (("Goal" :in-theory (enable equal-to-equal-list))))

  )

(defthm len-equiv-list-fix
  (len-equiv (list-fix x) x))

(defthm nth-equiv-list-fix
  (nth-equiv (list-fix x) x))

(defthm end-equiv-true-list-fix
  (end-equiv (true-list-fix x) nil)
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defun ens-equiv (x y)
  (declare (xargs :guard t))
  (and (len-equiv x y)
       (nth-equiv x y)))

(defthmd pretty-sure
  (equal (ens-equiv x y)
         (equal (list-fix x)
                (list-fix y)))
  :hints (("Goal" :in-theory (enable equal-to-nth-equiv-reduction)
           :restrict ((equal-to-nth-equiv-reduction
                       ((x (list-fix x))
                        (y (list-fix y))))))))

(defequiv ens-equiv)

(defrefinement ens-equiv len-equiv)
(defrefinement ens-equiv nth-equiv)

#+joe
(defrefinement ens-equiv list-equiv
  :hints (("Goal" :in-theory (e/d (list-equiv  pretty-sure) (ens-equiv)))))

(defrefinement list-equiv ens-equiv)

(defun ens-p (x)
  (declare (xargs :guard t))
  (true-listp x))

(defun ens-fix (x)
  (declare (type t x))
  (true-list-fix x))

(defthm ens-equiv-ens-fix
  (ens-equiv (ens-fix x) x)
  :hints (("Goal" :in-theory (e/d (list-equiv pretty-sure) ()))))

(in-theory (disable ens-equiv))

;;
;; So .. if you were to add end-equiv the fixing function
;; is provably the identity and ens-p is actually right.
;;
;;(def::fix ens-fix ens-equiv
;;  :type ens-p
;;  )

(defthm ens-p-implies-ens-fix-identity
  (implies
   (ens-p x)
   (equal (ens-fix x) x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthmd ens-equiv-to-ens-fix
  (equal (ens-equiv x y)
         (equal (ens-fix x)
                (ens-fix y)))
  :hints (("Goal" :in-theory (enable pretty-sure))))

(defcong ens-equiv equal (ens-fix x) 1
  :hints (("Goal" :in-theory (enable ens-equiv-to-ens-fix))))

(in-theory (disable ens-fix))

(def::type-fty ens
  :type-p ens-p
  :fix  ens-fix
  :fix! ens-fix
  :equiv ens-equiv
  :fix-constants nil)

;;
;; Ensemble
;;
(def::un max-ens-index (x)
  (declare (xargs :fty ((ens) nat)))
  (nfix (1- (len x))))

(defcong len-equiv equal (max-ens-index x) 1)

(in-theory (disable max-ens-index))

(def::und ensemble-index (i ens)
  (declare (xargs :signature ((t t) natp)
                  :congruence ((nat-equiv len-equiv) equal)))
  (min (nfix i) (nfix (1- (len (list-fix ens))))))

(defun ensemble-index-p (x ens)
  (declare (type t x ens))
  (and (natp x)
       (<= x (max-ens-index (ens-fix ens)))))

(defthm ensemble-index-upper-bound-2
  (<= (ensemble-index x ens) (max-ens-index ens))
  :rule-classes ((:linear :trigger-terms ((ensemble-index x ens))))
  :hints (("Goal" :in-theory (enable max-ens-index ensemble-index))))

(defthm ensemble-index-upper-bound-1
  (<= (ensemble-index i ens) (nfix i))
  :rule-classes ((:linear :trigger-terms ((ensemble-index i ens))))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(defthm ensmble-index-p-0
  (ensemble-index-p 0 ens)
  :rule-classes (:rewrite :type-prescription))

(defthm ensmble-index-p-ensemble-index
  (ensemble-index-p (ensemble-index x ens) ens)
  :rule-classes (:rewrite :type-prescription))

(defthmd strictly-less-means-reduce-1
  (implies
   (< (ensemble-index x ens) (max-ens-index ens))
   (equal (ensemble-index x ens)
          (nfix x)))
  :hints (("goal" :in-theory (enable ensemble-index max-ens-index))))

(defthm strictly-less-means-reduce-2
  (implies
   (<= (nfix x) (max-ens-index ens))
   (equal (ensemble-index x ens)
          (nfix x)))
  :hints (("goal" :in-theory (enable max-ens-index ensemble-index))))

(defthm ensemble-index-ensemble-index
  (equal (ensemble-index (ensemble-index i ens) ens)
         (ensemble-index i ens))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((ensemble-index (ensemble-index i ens) ens)))
                 (:forward-chaining :trigger-terms ((ensemble-index (ensemble-index i ens) ens)))))

(defthm ensemble-index-nfix
  (equal (ensemble-index (nfix i) ens)
         (ensemble-index i ens))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((ensemble-index (nfix i) ens)))
                 (:forward-chaining :trigger-terms ((ensemble-index (nfix i) ens)))))

(defthm ensemble-index-ensemble-index-p
  (implies
   (ensemble-index-p x ens)
   (equal (ensemble-index x ens) x))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable MAX-ENS-INDEX ensemble-index))))

(defthm ensemble-index-p-max-ens-index
  (ensemble-index-p (max-ens-index ens) ens))

(defthm ensemble-index-plus
  (implies
   (< (ENSEMBLE-INDEX X ENS)
      (MAX-ENS-INDEX ENS))
   (ensemble-index-p (+ 1 (ENSEMBLE-INDEX X ENS)) ens))
  :rule-classes (:forward-chaining))

(defthm ensemble-index-minus
  (implies
   (< 0 (ENSEMBLE-INDEX X ENS))
   (ensemble-index-p (+ -1 (ENSEMBLE-INDEX X ENS)) ens))
  :rule-classes (:forward-chaining))

(defthmd equal-ensemble-index-bootstrap
  (implies
   (syntaxp (not (and (consp i) (equal (car i) 'ensemble-index))))
   (iff (equal (ENSEMBLE-INDEX J ENS) I)
        (and (ensemble-index-p I ens)
             (equal (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX I ENS)))))
  :hints (("Goal" :in-theory (enable MAX-ENS-INDEX ENSEMBLE-INDEX))))

(defun unwrap-ensemble-index (x)
  (case-match x
    ((`ensemble-index x) x)
    (& x)))

(defun meta-max-ens-index-p (x)
  (case-match x
    ((`max-ens-index &) t)
    (& nil)))

(defun good-index-rewrite-order (x y)
  (declare (xargs :mode :program))
  (let ((x (unwrap-ensemble-index x))
        (y (unwrap-ensemble-index y)))
    (or (good-rewrite-order x y)
        (and (not (equal x y))
             (meta-max-ens-index-p y)))))

(in-theory (disable ensemble-index-p))

(theory-invariant (incompatible (:rewrite equal-ensemble-index-bootstrap)
                                (:rewrite ensemble-index-ensemble-index-p)))
(theory-invariant (incompatible (:rewrite equal-ensemble-index-bootstrap)
                                (:linear ENSEMBLE-INDEX-UPPER-BOUND-1)))
(theory-invariant (incompatible (:rewrite equal-ensemble-index-bootstrap)
                                (:linear ENSEMBLE-INDEX-UPPER-BOUND-2)))
(theory-invariant (incompatible (:rewrite equal-ensemble-index-bootstrap)
                                (:rewrite STRICTLY-LESS-MEANS-REDUCE-2)))
(theory-invariant (incompatible (:rewrite equal-ensemble-index-bootstrap)
                                (:rewrite STRICTLY-LESS-MEANS-REDUCE-1)))

(defmacro ensemble-index-equiv-theory (&key (e 'nil) (d 'nil))
  `(e/d (equal-ensemble-index-bootstrap ,@e)
        (ensemble-index-ensemble-index-p
         ENSEMBLE-INDEX-UPPER-BOUND-1
         ENSEMBLE-INDEX-UPPER-BOUND-2
         STRICTLY-LESS-MEANS-REDUCE-2
         STRICTLY-LESS-MEANS-REDUCE-1
         ,@d)))

(defthm ensemble-index-ordering
  (implies
   (and
    (< (ensemble-index i ens)
       (ensemble-index j ens))
    (< 0 (nfix i))
    (< (nfix k) (nfix i)))
   (< (ensemble-index k ens)
      (ensemble-index j ens)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable ensemble-index))))

(defthm ensemble-index-step
  (implies (and (< 0 (nfix i))
                (< (ensemble-index j ens)
                   (ensemble-index i ens)))
           (<= (ensemble-index j ens)
               (ensemble-index (+ -1 (nfix i)) ens)))
  :rule-classes (:linear)
  :hints (("goal" :in-theory (enable ensemble-index))))

(defthmd nfix-ensemble-index
  (equal (nfix (ensemble-index i ens))
         (ensemble-index i ens))
  :rule-classes ((:linear :trigger-terms ((ensemble-index i ens)))))

(defthm degenerate-ensemble-index
  (implies
   (equal (len ens) 1)
   (equal (ensemble-index x ens) 0))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(def::linear ensemble-index-strict-ordering-implies-index-strict-ordering-linear
  (implies
   (and
    (syntaxp (not (equal x y)))
    (<= (nfix y) (nfix x)))
   (<= (ensemble-index y ens) (ensemble-index x ens)))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(in-theory (disable ensemble-index-strict-ordering-implies-index-strict-ordering-linear))

(defthm ensemble-index-strict-ordering-implies-index-strict-ordering-fwd
  (implies
   (< (ensemble-index x ens) (ensemble-index y ens))
   (< (nfix x) (nfix y)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ensemble-index))))

(defthm dissimilar-ensemble-index-implies-dissimilar-index
  (implies
   (not (equal (ensemble-index x ens) (ensemble-index y ens)))
   (not (equal (nfix x) (nfix y))))
  :hints (("Goal" :in-theory (enable ensemble-index)))
  :rule-classes (:forward-chaining))

;;
;; get-uav
;;

(def::un get-uav (i ens)
  (declare (xargs :signature ((t t) uav-p)
                  :congruence ((nat-equiv ens-equiv) equal)))
  (UAV-fix! (nth (ensemble-index i ens) (list-fix ens))))

(defun-sk get-uav-equiv (x y)
  (declare (xargs :guard t))
  (forall (i) (equal (get-uav i x) (get-uav i y)))
  :strengthen t)

(quant::congruence get-uav-equiv (x y)
  (forall (i) (equal (get-uav i x) (get-uav i y)))
  :congruences ((x ens-equiv)
                (y ens-equiv)))

(in-theory (disable get-uav-equiv))

(defthmd get-uav-equiv-implication
  (implies
   (get-uav-equiv x y)
   (equal (get-uav i x)
          (get-uav i y)))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :use get-uav-equiv-necc)))


(encapsulate
    ()

  (local
   (encapsulate
       ()

     (in-theory (enable get-uav-equiv-implication))

     (defthm get-uav-equiv-id
       (get-uav-equiv x x)
       :hints (("Goal" :expand (get-uav-equiv x x))))
     
     (defthm get-uav-equiv-commutes
       (IMPLIES
        (GET-UAV-EQUIV X Y)
        (GET-UAV-EQUIV Y X))
       :hints (("Goal" :expand (GET-UAV-EQUIV Y X))))
     
     (defthm get-uav-equiv-transitive
       (IMPLIES
        (AND (GET-UAV-EQUIV X Y)
             (GET-UAV-EQUIV Y Z))
        (GET-UAV-EQUIV X Z))
       :hints (("Goal" :expand (GET-UAV-EQUIV X Z))))

     ))
     
  (defequiv get-uav-equiv)

  )

(defrefinement ens-equiv get-uav-equiv)

(defcong get-uav-equiv equal (get-uav i ens) 2
  :hints (("Goal" :in-theory (enable get-uav-equiv-implication))))

(defthm get-uav-ensemble-index-congruence
  (implies
   (equal (ensemble-index i ens) j)
   (equal (get-uav i ens)
          (get-uav j ens)))
  :rule-classes ((:forward-chaining :trigger-terms ((get-uav i ens))))
  :hints (("goal" :in-theory (enable get-uav))))

(defthm get-uav-ensemble-index-reduction
  (equal (get-uav (ensemble-index i ens) ens)
         (get-uav i ens))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((get-uav (ensemble-index i ens) ens)))))
  
(defthmd get-uav-ensemble-index!
  (implies
   (syntaxp (symbolp i))
   (equal (get-uav i ens)
          (get-uav (ensemble-index i ens) ens)))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(theory-invariant (incompatible (:rewrite get-uav-ensemble-index-reduction)
                                (:rewrite get-uav-ensemble-index!)))

(defmacro ensemble-hyps-imply (body)
  `(and
    (implies
     (< (ifix i) 0)
     ,body)
    (implies
     (and
      (syntaxp (symbolp i))
      (<= (+ -1 (len ens)) (nfix i)))
     ,body)
    (implies
     (and
      (<= (len ens) (nfix i))
      (< 0 (len ens)))
     ,body)
    (implies
     (and
      (<= (len ens) (nfix i))
      (equal (len ens) 0)
      (syntaxp (or (not (quotep i)) (not (equal (cadr i) 0)))))
     ,body)))

(defthmd get-uav-ensemble-index
  (ensemble-hyps-imply
   (equal (get-uav i ens)
          (get-uav (ensemble-index i ens) ens))))

(theory-invariant (incompatible (:rewrite get-uav-ensemble-index-reduction)
                                (:rewrite get-uav-ensemble-index)))

(defthmd neighbor-too
  (implies
   (<= (len ens) (nfix x))
   (equal (get-uav (+ -1 (nfix x)) ens)
          (get-uav (+ -1 (len ens)) ens)))
  :hints (("Goal" :in-theory (enable nfix get-uav ensemble-index))))

(in-theory (disable get-uav))

;;
;; set-uav
;; 
(def::un set-uav (i uav ens)
  (declare (xargs :congruence ((nat-equiv uav-equiv nil) equal)
                  :congruence ((nil nil ens-equiv) equal))
           (type (satisfies natp) i)
           (type (satisfies uav-p) uav))
  (let ((ens (ens-fix ens)))
    (if (not (consp ens)) ens
      (ens-fix (update-nth (ensemble-index i ens) (UAV-fix uav) (list-fix ens))))))

(defthm len-set-uav
  (equal (len (set-uav i uav ens))
         (len ens))
  :hints (("Subgoal 2" :in-theory (enable ensemble-index))))

(in-theory (disable set-uav))

(defthm len-equiv-set-uav
  (len-equiv (set-uav i uav ens) ens)
  :hints (("Goal" :do-not-induct t
           :in-theory (enable len-equiv))))

(defthm get-uav-set-uav
  (equal (get-uav i (set-uav j uav ens))
         (if (and (equal (ensemble-index i ens)
                         (ensemble-index j ens))
                  (consp ens))
             (uav-fix uav)
           (get-uav i ens)))
  :hints (("Goal" :in-theory (enable get-uav))
          (and stable-under-simplificationp
               '(:in-theory (enable set-uav)))))

;;
;;
(def::und left-moving-uav-split-location (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (UAV->left-moving-uav-split-location (get-uav i ens)))

(defthm left-moving-uav-split-location-ensemble-index
  (equal (LEFT-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)
         (LEFT-MOVING-UAV-SPLIT-LOCATION x ens))
  :hints (("Goal" :in-theory (e/d (LEFT-MOVING-UAV-SPLIT-LOCATION) nil)))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((LEFT-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)))
                 (:forward-chaining :trigger-terms ((LEFT-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)))))

(def::und right-moving-uav-split-location (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (UAV->right-moving-uav-split-location (get-uav i ens)))

(defthm right-moving-uav-split-location-ensemble-index
  (equal (RIGHT-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)
         (RIGHT-MOVING-UAV-SPLIT-LOCATION x ens))
  :hints (("Goal" :in-theory (e/d (RIGHT-MOVING-UAV-SPLIT-LOCATION) nil)))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((right-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)))
                 (:forward-chaining :trigger-terms ((right-MOVING-UAV-SPLIT-LOCATION (ENSEMBLE-INDEX X ENS) ens)))))

(defthm indexed-uav-split-location-ordering
  (< (left-moving-uav-split-location i uav)
     (right-moving-uav-split-location i uav))
  :hints (("Goal" :in-theory (enable right-moving-uav-split-location
                                     left-moving-uav-split-location)))
  :rule-classes (:linear))

(def::und left-moving-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (< (UAV->dx (get-uav i ens)) 0))

(defthmd left-moving-ensemble-index!
  (implies
   (syntaxp (symbolp i))
   (equal (left-moving-p i ens)
          (left-moving-p (ensemble-index i ens) ens)))
  :hints (("Goal" :in-theory (e/d (left-moving-p) nil))))

(defthm left-moving-p-ensemble-index
  (equal (left-moving-p (ensemble-index x ens) ens)
         (left-moving-p x ens))
  :hints (("Goal" :in-theory (e/d (left-moving-p) nil)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :corollary
                  (implies
                   (left-moving-p (ensemble-index x ens) ens)
                   (left-moving-p x ens)))))

(defthm left-moving-p-ensemble-index-forward
  (implies
   (and
    (left-moving-p i ens)
    (equal (ensemble-index i ens) j))
   (left-moving-p j ens))
  :rule-classes (:forward-chaining)
  :hints (("goal" :in-theory (e/d (get-uav-ensemble-index!
                                   left-moving-p)
                                  (get-uav-ensemble-index-reduction)))))

(def::un right-moving-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (not (left-moving-p i ens)))

(def::und current-location (i ens)
  (declare (xargs :signature ((t t) rationalp)
                  :congruence ((nat-equiv ens-equiv) equal)))
  (UAV->xx (get-uav i ens)))

(defthm current-location-ensemble-index
  (equal (current-location (ensemble-index i ens) ens)
         (current-location i ens))
  :hints (("Goal" :in-theory (e/d (current-location) nil)))
  :rule-classes (:rewrite (:linear :trigger-terms ((current-location (ensemble-index i ens) ens)))))

(defthmd current-location-ensemble-index!
  (implies
   (syntaxp (symbolp i))
   (equal (current-location i ens)
          (current-location (ensemble-index i ens) ens)))
  :hints (("Goal" :in-theory (e/d (current-location) nil))))

(theory-invariant (incompatible (:rewrite current-location-ensemble-index)
                                (:rewrite current-location-ensemble-index!)))

(defthm current-location-ensemble-index-equiv
  (implies
   (equal (ensemble-index i ens) j)
   (equal (current-location i ens)
          (current-location j ens)))
  :rule-classes ((:linear :trigger-terms ((current-location i ens))))
  :hints (("Goal" :in-theory (e/d (current-location-ensemble-index!)
                                  (current-location-ensemble-index)))))

(defthm current-location-ensemble-index-equiv-rewrite
  (implies
   (equal (ensemble-index i ens) (ensemble-index j ens))
   (iff (equal (current-location i ens)
               (current-location j ens)) t)))

(def::und LeftPerimeterGuess (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (UAV->LP (get-uav i ens)))
  
(def::und RightPerimeterGuess (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (UAV->RP (get-uav i ens)))
  
(def::und LeftCountGuess (i ens)
  (declare (xargs :fty ((nat ens) nat)))
  (UAV->LC (get-uav i ens)))

(def::und RightCountGuess (i ens)
  (declare (xargs :fty ((nat ens) nat)))
  (UAV->RC (get-uav i ens)))

(defthm LEFTCOUNTGUESS-ENSEMBLE-INDEX
  (equal (LEFTCOUNTGUESS (ENSEMBLE-INDEX MIN ENS) ENS)
         (LEFTCOUNTGUESS MIN ENS))
  :hints (("Goal" :in-theory (e/d (leftcountguess) nil))))

(defthm LEFTPERIMETERGUESS-ENSEMBLE-INDEX
  (equal (LEFTPERIMETERGUESS (ENSEMBLE-INDEX MIN ENS) ENS)
         (LEFTPERIMETERGUESS MIN ENS))
  :hints (("Goal" :in-theory (e/d (leftperimeterguess) nil))))

(defthm RIGHTCOUNTGUESS-ENSEMBLE-INDEX
  (equal (RIGHTCOUNTGUESS (ENSEMBLE-INDEX MIN ENS) ENS)
         (RIGHTCOUNTGUESS MIN ENS))
  :hints (("Goal" :in-theory (e/d (rightcountguess) nil))))

(defthm RIGHTPERIMETERGUESS-ENSEMBLE-INDEX
  (equal (RIGHTPERIMETERGUESS (ENSEMBLE-INDEX MIN ENS) ENS)
         (RIGHTPERIMETERGUESS MIN ENS))
  :hints (("Goal" :in-theory (e/d (rightperimeterguess) nil))))

(def::und seg-size (i ens)
  (declare (xargs :fty ((nat ens) prat)))
  (UAV->seg-size (get-uav i ens)))

(def::und index-guess (i ens)
  (declare (xargs :fty ((nat ens) nat)))
  (UAV->LC (get-uav i ens)))

(def::type-str Escort
  ((LP rational)
   (LC nat)
   (Li nat)
   (xx rational)
   (dx sign)
   (Ri nat)
   (RC nat)
   (RP rational)))

(defmacro Escort* (uav &key (LP 'nil) (LC 'nil) (Li 'nil) (xx 'nil) (dx 'nil) (Ri 'nil) (RC 'nil) (RP 'nil))
  `(let ((LP  ,(or LP `(Escort->LP ,uav)))
         (LC  ,(or LC `(Escort->LC ,uav)))
         (Li  ,(or Li `(Escort->Li ,uav)))
         (xx  ,(or xx `(Escort->xx ,uav)))
         (dx  ,(or dx `(Escort->dx ,uav)))
         (Ri  ,(or Ri `(Escort->Ri ,uav)))
         (RC  ,(or RC `(Escort->RC ,uav)))
         (RP  ,(or RP `(Escort->RP ,uav))))
     (Escort LP LC Li xx dx Ri RC RP)))

(defmacro Escort! (&key (LP 'nil LP-p) (LC 'nil LC-p) (Li 'nil Li-p) (xx 'nil xx-p) (dx 'nil dx-p) (Ri 'nil Ri-p) (RC 'nil RC-p) (RP 'nil RP-p))
  (declare (xargs :guard (and LP-p LC-p Li-p xx-p dx-p Ri-p RC-p RP-p))
           (ignorable LP-p LC-p Li-p xx-p dx-p Ri-p RC-p RP-p))
  `(Escort* nil :LP ,LP :LC ,LC :Li ,Li :xx ,xx :dx ,dx :Ri ,Ri :RC ,RC :RP ,RP))

(def-b*-binder Escort*
  :body (patbind-fn args '((LP . Escort->LP)
                           (LC . Escort->LC)
                           (Li . Escort->Li)
                           (xx . Escort->xx)
                           (dx . Escort->dx)
                           (Ri . Escort->Ri)
                           (RC . Escort->RC)
                           (RP . Escort->RP))
                    forms rest-expr))

(defun wfEscort-p (x)
  (declare (type t x))
  (and (escort-p x)
       (< (escort->Li x) (escort->Ri x))))

(defthm implies-wfEscort-p
  (implies
   (and (escort-p x) (< (escort->Li x) (escort->Ri x)))
   (wfEscort-p x)))

(defthm wfEscort-p-implies
  (implies
   (wfEscort-p x)
   (and (escort-p x) (< (escort->Li x) (escort->Ri x))))
  :rule-classes (:forward-chaining))

(in-theory (disable wfEscort-p))

(def::un escort-left-index (x ens)
  (declare (xargs :fty ((nat any) nat)
                  :measure (nfix x)
                  :hints (("Goal" :in-theory (enable ENSEMBLE-INDEX)))))
  (let ((x (ensemble-index x ens)))
    (if (zp x) x
      (b* ((left  (1- x))
           (right x)
           (Luav  (get-uav left ens))
           (Ruav  (get-uav right ens))
           ((UAV* :xx Lx :dx Ldx) Luav)
           ((UAV* :xx Rx :dx Rdx) Ruav))
        (if (not (equal Lx Rx)) x
          (if (not (equal Ldx Rdx)) x
            (escort-left-index left ens)))))))

(defthm escort-left-index-ensemble-index
  (equal (escort-left-index (ensemble-index x ens) ens)
         (escort-left-index x ens))
  :hints (("Goal" :expand ((escort-left-index (ensemble-index x ens) ens)
                           (escort-left-index x ens))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((escort-left-index (ensemble-index x ens) ens)))
                 (:forward-chaining :trigger-terms ((escort-left-index (ensemble-index x ens) ens)))))
          

(encapsulate
    ()

  (local (in-theory (disable escort-left-index)))

  (local
   (defthm escort-left-index-ensemble-index!
     (implies
      (syntaxp (symbolp x))
      (equal (escort-left-index x ens)
             (escort-left-index (ensemble-index x ens) ens)))))

  (local (in-theory (disable escort-left-index-ensemble-index)))
  
  (defthm escort-left-index-ensemble-index-equiv
    (implies
     (equal (ensemble-index x ens) y)
     (equal (escort-left-index x ens)
            (escort-left-index y ens)))
    :rule-classes ((:linear :trigger-terms ((escort-left-index x ens)))
                   (:forward-chaining :trigger-terms ((escort-left-index x ens)))))
    
  )

(encapsulate
    ()
  
  (local
   (defthm trope
     (implies
      (syntaxp (symbolp ens))
      (equal (escort-left-index x ens)
             (escort-left-index x (ens-fix ens))))
     :hints (("Goal" :induct (escort-left-index x ens)
              :expand (escort-left-index x (ens-fix ens))))))
  
  (defthm ens-equiv-0-implies-equal-escort-left-index
    (implies (ens-equiv x1 x1-equal)
             (equal (escort-left-index x2 x1)
                    (escort-left-index x2 x1-equal)))
    :hints (("goal" :in-theory (enable trope)))
    :rule-classes :congruence)
  
  )

(defthm escort-left-index-lower-bound
  (<= 0 (escort-left-index x ens))
  :rule-classes (:linear))

(defthm escort-left-index-upper-bound
  (<= (escort-left-index x ens) (ensemble-index x ens))
  :rule-classes ((:linear :trigger-terms ((escort-left-index x ens)))))

(defthm ensemble-index-p-escort-left-index
  (ensemble-index-p (escort-left-index x ens) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(defthm ensemble-index-escort-left-index
  (equal (ensemble-index (escort-left-index x ens) ens)
         (escort-left-index x ens)))
                                          
;; #+joe
;; (defthm natp-max-ens-index
;;   (implies
;;    (< 0 (len ens))
;;    (<= 0 (max-ens-index ens)))
;;   :rule-classes (:linear))

(def::un escort-right-index (x ens)
  (declare (xargs :fty ((nat any) nat)
                  :guard (ens-p ens)
                  :hints (("Goal" :in-theory (enable ensemble-index max-ens-index)))
                  :measure (- (max-ens-index ens) (ensemble-index x ens))))
  (let ((x (ensemble-index x ens)))
    (if (<= (max-ens-index ens) x) (max-ens-index ens) ;; x
      (b* ((left  x)
           (right (1+ x))
           (Luav  (get-uav left ens))
           (Ruav  (get-uav right ens))
           ((UAV* :xx Lx :dx Ldx) Luav)
           ((UAV* :xx Rx :dx Rdx) Ruav))
        (if (not (equal Lx Rx)) x
          (if (not (equal Ldx Rdx)) x
            (escort-right-index right ens)))))))

(defthm escort-right-index-ensemble-index
  (equal (escort-right-index (ensemble-index x ens) ens)
         (escort-right-index x ens))
  :hints (("Goal" :expand ((escort-right-index (ensemble-index x ens) ens)
                           (escort-right-index x ens))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((escort-right-index (ensemble-index x ens) ens)))
                 (:forward-chaining :trigger-terms ((escort-right-index (ensemble-index x ens) ens)))))

(encapsulate
    ()

  (local (in-theory (disable escort-right-index)))
  
  (local
   (defthm escort-right-index-ensemble-index!
     (implies
      (syntaxp (symbolp x))
      (equal (escort-right-index x ens)
             (escort-right-index (ensemble-index x ens) ens)))))

  (local (in-theory (disable escort-right-index-ensemble-index)))
  
  (defthm escort-right-index-ensemble-index-equiv
    (implies
     (equal (ensemble-index x ens) y)
     (equal (escort-right-index x ens)
            (escort-right-index y ens)))
    :rule-classes ((:linear :trigger-terms ((escort-right-index x ens)))
                   (:forward-chaining :trigger-terms ((escort-right-index x ens)))))
    
  )

(encapsulate
    ()

  (local
   (defthm trope
     (implies
      (syntaxp (symbolp ens))
      (equal (escort-right-index x ens)
             (escort-right-index x (ens-fix ens))))
     :hints (("Goal" :induct (escort-right-index x ens))
             (and stable-under-simplificationp
                  '(:expand (ESCORT-RIGHT-INDEX X (ENS-FIX ENS)))))))
  
  (defthm ens-equiv-0-implies-equal-escort-right-index
    (implies (ens-equiv x1 x1-equal)
             (equal (escort-right-index x2 x1)
                    (escort-right-index x2 x1-equal)))
    :hints (("goal" :in-theory (enable trope)))
    :rule-classes :congruence)
  
  )

;;
;; (defthm negative-escort-right-index
;;   (implies
;;    (< (escort-right-index x ens) 0)
;;    (and (<= (1- (len ens)) (nfix x))
;;         (< (1- (len ens)) 0)))
;;   :rule-classes (:forward-chaining :linear))

;;
;; #+joe
;; (defthm positive-escort-right-index
;;   (<= 0 (escort-right-index x ens)))

(defthm escort-right-index-lower-bound-rough
  (implies
   (<= (nfix x) (max-ens-index ens))
   (<= (nfix x) (escort-right-index x ens)))
  :rule-classes ((:linear :trigger-terms ((escort-right-index x ens)))))

(defthm escort-right-index-lower-bound
  (<= (ensemble-index x ens) (escort-right-index x ens))
  :rule-classes ((:linear :trigger-terms ((escort-right-index x ens)))))

(defthm escort-right-index-upper-bound
  ;;(implies ;;
  ;; (<= (nfix x) (max-ens-index ens)) ;;
  (<= (escort-right-index x ens) (max-ens-index ens))
  :rule-classes ((:linear :trigger-terms ((escort-right-index x ens)))))

(defthm ensemble-index-p-escort-right-index
  (ensemble-index-p (escort-right-index x ens) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(defthm escort-right-index-bound-rewrite
  (iff (< (ESCORT-RIGHT-INDEX X ENS) (nfix x))
       (< (max-ens-index ens) (nfix x))))

;; Does this really help?
;; (defthm smaller-right-index
;;   (implies
;;    (< (escort-right-index x ens) (nfix x))
;;    (< (1- (len ens)) (nfix x)))
;;   :hints (("Goal" :use escort-right-index-lower-bound))
;;   :rule-classes (:forward-chaining (:linear :trigger-terms ((escort-right-index x ens)))))

(defthm ensemble-index-escort-right-index
  (equal (ensemble-index (escort-right-index x ens) ens)
         (escort-right-index x ens)))

(def::un get-escort (x ens)
  (declare (xargs :fty ((nat ens) Escort)))
  (b* ((xuav  (get-uav x ens))
       ((UAV* :xx xx :dx dx) xuav)
       (left  (escort-left-index x ens))
       (Luav  (get-uav left ens))
       ((UAV* :LP LP :LC LC) Luav)
       (right (escort-right-index x ens))
       (Ruav  (get-uav right ens))
       ((UAV* :RC RC :RP RP) Ruav))
    (Escort! :LP  LP
             ;;
             ;; So LC/RC reflect either the current UAV
             ;; or the ensemble.  The nice thing about
             ;; having them reflect the entire ensemble
             ;; is that the escort abstraction will be the same for
             ;; each member of the escort.
             ;; 
             :LC  LC ;; (+ LC (- (ensemble-index x ens) left))
             :Li  left
             :xx  xx
             :dx  dx
             :Ri  right
             :RC  RC ;; (+ RC (- right (ensemble-index x ens)))
             :RP  RP)))

(defthm get-escort-ensemble-index
  (equal (get-escort (ensemble-index x ens) ens)
         (get-escort x ens)))

(def::und Escort->size (e)
  (declare (xargs :fty ((Escort) nat)))
  (b* (((Escort* :Li Li :Ri Ri) e))
    (+ 1 (nfix (- Ri Li)))))

(defthm positive-escort-size
  (< 0 (Escort->size e))
  :hints (("Goal" :in-theory (enable Escort->size)))
  :rule-classes (:linear))

(def::und Escort->seg-size (e)
  (declare (xargs :fty ((Escort) prat)))
  (b* (((Escort* :LP LP :LC LC :RC RC :RP RP) e)
       (S (Escort->size e)))
    (seg-size-fn LP LC S RC RP)))

(def::und Escort->left-moving-escort-split-location (e)
  (declare (xargs :fty ((Escort) rational)))
  (+ (Escort->LP e) (left-moving-uav-split-offset-fn (+ (Escort->LC e) (Escort->size e) -1) (Escort->seg-size e))))

(def::und Escort->right-moving-escort-split-location (e)
  (declare (xargs :fty ((Escort) rational)))
  (+ (Escort->LP e) (right-moving-uav-split-offset-fn (Escort->LC e) (Escort->seg-size e))))

(def::un left-moving-escort-split-location (x ens)
  (declare (xargs :fty ((nat ens) rational)))
  (Escort->left-moving-escort-split-location (get-escort x ens)))

(def::un right-moving-escort-split-location (x ens)
  (declare (xargs :fty ((nat ens) rational)))
  (Escort->right-moving-escort-split-location (get-escort x ens)))

#+Joe
(with-arithmetic
 (defthmd joker
   (implies
    (and
     (< 0 (rfix ss))
     (<= (ifix i) (ifix j)))
    (< (LEFT-MOVING-UAV-SPLIT-OFFSET-FN i ss)
       (RIGHT-MOVING-UAV-SPLIT-OFFSET-FN j ss)))))

#+joe
(with-arithmetic
 (defthm left-right-split-location-separation
   (< (right-moving-escort-split-location x ens)
      (left-moving-escort-split-location x ens))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (ESCORT->LEFT-MOVING-ESCORT-SPLIT-LOCATION
                             ESCORT->RIGHT-MOVING-ESCORT-SPLIT-LOCATION)
                            (left-moving-uav-split-offset-fn
                             right-moving-uav-split-offset-fn
                             )))
           (pattern-hint
            (:and
             (:term (LEFT-MOVING-UAV-SPLIT-OFFSET-FN i ss))
             (:term (RIGHT-MOVING-UAV-SPLIT-OFFSET-FN j ss)))
            :use ((:instance joker
                             (ss ss)
                             (i i)
                             (j j)))))))

(def::un meta-left-escort-count (x ens)
  (declare (xargs :fty ((nat ens) nat)))
  (b* ((e (get-escort x ens))
       ((Escort* :Li Li) e))
    (nfix (- (ensemble-index x ens) Li))))
       
(defthm meta-left-escort-count-ensemble-index
  (equal (meta-left-escort-count (ensemble-index x ens) ens)
         (meta-left-escort-count x ens)))

(def::un meta-right-escort-count (x ens)
  (declare (xargs :fty ((nat ens) nat)))
  (b* ((e (get-escort x ens))
       ((Escort* :Ri Ri) e))
    (nfix (- Ri (ensemble-index x ens)))))

(defthm meta-right-escort-count-ensemble-index
  (equal (meta-right-escort-count (ensemble-index x ens) ens)
         (meta-right-escort-count x ens)))

(def::un meta-left-neighbor-index (x ens)
  (declare (xargs :fty ((nat ens) int)))
  (- (ensemble-index x ens) (+ 1 (meta-left-escort-count x ens))))

(def::un meta-right-neighbor-index (x ens)
  (declare (xargs :fty ((nat ens) int)))
  (+ (ensemble-index x ens) (+ 1 (meta-right-escort-count x ens))))


(defthmd simpler-meta-left-neighbor-index
  (equal (meta-left-neighbor-index x ens)
         (+ (Escort->Li (get-escort x ens)) -1))
  :hints (("Goal" :do-not-induct t)))

(defthmd oob
  (implies
   (<= (max-ens-index ens) (nfix x))
   (equal (ESCORT-RIGHT-INDEX X ENS) (max-ens-index ens)))
  :hints (("Goal" :in-theory (enable nfix STRICTLY-LESS-MEANS-REDUCE-1)
           :expand (ESCORT-RIGHT-INDEX X ENS))))

(defthmd simpler-meta-right-neighbor-index
  (equal (meta-right-neighbor-index x ens)
         (if (< (max-ens-index ens) (nfix x)) (+ (ensemble-index x ens) 1) ;;
           (+ (Escort->Ri (get-escort x ens)) 1)))
  :hints (("Goal" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-1)
           :do-not-induct t)))

(def::un meta-leftmost-escort-p (x ens)
  (declare (xargs :fty ((nat ens) bool)))
  (equal (meta-left-escort-count x ens) (nfix x)))

(def::un meta-rightmost-escort-p (x ens)
  (declare (xargs :fty ((nat ens) bool)))
  (equal (+ (nfix x) (meta-right-escort-count x ens)) (max-ens-index ens)))

(def::un meta-escort-size (x ens)
  (declare (xargs :fty ((nat ens) nat)))
  (+ 1 (meta-left-escort-count x ens) (meta-right-escort-count x ens)))

(def::un leftmost-escort-uav-index-guess (x ens)
  (declare (xargs :fty ((nat ens) int)))
  (- (index-guess x ens) (meta-left-escort-count x ens)))

(def::un rightmost-escort-uav-index-guess (x ens)
  (declare (xargs :fty ((nat ens) int)))
  (+ (index-guess x ens) (meta-right-escort-count x ens)))

(def::un within-escort-group-p (i x ens)
  (declare (xargs :signature ((t t t) booleanp)
                  :guard (ens-p ens)
                  :congruence ((int-equiv int-equiv nil) equal)))
  (let ((i (nfix i))
        (x (nfix x)))
    (and
     (<= (- (ensemble-index x ens) (meta-left-escort-count x ens)) (ensemble-index i ens))
     (<= (ensemble-index i ens) (+ (ensemble-index x ens) (meta-right-escort-count x ens))))))

(defthm within-escort-group-p-ensemble-index
  (and (equal (within-escort-group-p i (ensemble-index x ens) ens)
              (within-escort-group-p i x ens))
       (equal (within-escort-group-p (ensemble-index i ens) x ens)
              (within-escort-group-p i x ens)))
  :hints (("Goal" :in-theory (disable meta-left-escort-count
                                      meta-right-escort-count))))

(defthmd test1
  (equal (escort-left-index x ens)
         (- (ensemble-index x ens) (meta-left-escort-count x ens))))

(defthmd test2
  (equal (+ (ensemble-index x ens) (meta-right-escort-count x ens))
         (if (<= (nfix x) (max-ens-index ens)) (escort-right-index x ens)
           (ensemble-index x ens)))
  :hints (("Goal" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-1))))

(defthm simple-within-escort-group
  (iff (within-escort-group-p i x ens)
       (and (<= (escort-left-index x ens) (ensemble-index i ens))
            (<= (ensemble-index i ens) (escort-right-index x ens)))))

(defthm escort-left-index-<=-ESCORT-RIGHT-INDEX
  (<= (ESCORT-LEFT-INDEX X ENS)
      (ESCORT-RIGHT-INDEX X ENS)))

(defthm within-escort-group-p-escort-left-index
  (within-escort-group-p (escort-left-index x ens) x ens)
  :rule-classes ((:forward-chaining :trigger-terms ((escort-left-index x ens)))))

(defthm within-escort-group-p-escort-right-index
  (within-escort-group-p (escort-right-index x ens) x ens)
  :rule-classes ((:forward-chaining :trigger-terms ((escort-right-index x ens)))))

(in-theory (disable within-escort-group-p))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     ;; (defun ensenble-index-equiv (x y ens)
     ;;   (equal (ENSEMBLE-INDEX x ENS)
     ;;          (ENSEMBLE-INDEX y ENS)))

     (defthm equal-nfix-max-ens-index
       (implies
        (equal (nfix x) (MAX-ENS-INDEX ENS))
        (equal (ensemble-index x ens)
               (ensemble-index (MAX-ENS-INDEX ENS) ens)))
       :rule-classes (:forward-chaining))

     ;; (defthm ensemble-index-equality-forward-1
     ;;   (implies
     ;;    (EQUAL (ENSEMBLE-INDEX I ENS) (NFIX X))
     ;;    (equal (ENSEMBLE-INDEX I ENS)
     ;;           (ENSEMBLE-INDEX X ENS)))
     ;;   :rule-classes ((:forward-chaining :trigger-terms ((EQUAL (ENSEMBLE-INDEX I ENS) (NFIX X))))))

     ;; (defthm ensemble-index-equality-forward-2
     ;;   (implies
     ;;    (EQUAL (ENSEMBLE-INDEX I ENS) 0)
     ;;    (equal (ENSEMBLE-INDEX I ENS)
     ;;           (ENSEMBLE-INDEX 0 ENS)))
     ;;   :rule-classes ((:forward-chaining :trigger-terms ((EQUAL (ENSEMBLE-INDEX I ENS) 0)))))

     ;; (defthm ensemble-index-equality-forward-3
     ;;   (implies
     ;;    (EQUAL (ENSEMBLE-INDEX I ENS) (MAX-ENS-INDEX ENS))
     ;;    (equal (ENSEMBLE-INDEX I ENS)
     ;;           (ENSEMBLE-INDEX (MAX-ENS-INDEX ENS) ENS)))
     ;;   :rule-classes ((:forward-chaining :trigger-terms ((EQUAL (ENSEMBLE-INDEX I ENS) (MAX-ENS-INDEX ENS))))))
     
     (defthmd included-in-escort-left-index-helper
       (implies
        (and
         (<= (escort-left-index i ens) (nfix x))
         (<= (nfix x) (ensemble-index i ens)))
        (and (equal (uav->xx (get-uav x ens))
                    (uav->xx (get-uav i ens)))
             (equal (uav->dx (get-uav x ens))
                    (uav->dx (get-uav i ens))
                    )))
       :hints (("Goal" :in-theory (enable get-uav-ensemble-index-congruence)
                :induct (escort-left-index i ens))
               (stable-p :in-theory (ensemble-index-equiv-theory))))

     (defthmd included-in-escort-left-index
       (implies
        (and
         (<= (escort-left-index i ens) (ensemble-index x ens))
         (<= (ensemble-index x ens) (ensemble-index i ens)))
        (and (equal (uav->xx (get-uav x ens))
                    (uav->xx (get-uav i ens)))
             (equal (uav->dx (get-uav x ens))
                    (uav->dx (get-uav i ens))
                    )))
       :hints (("Goal" :use (:instance included-in-escort-left-index-helper
                                       (x (ensemble-index x ens))))))
     
     (defthmd included-in-escort-right-index-helper
       (implies
        (and
         (<= (nfix x) (escort-right-index i ens))
         (<= (ensemble-index i ens) (nfix x)))
        (and (equal (uav->xx (get-uav x ens))
                    (uav->xx (get-uav i ens))
                    )
             (equal (uav->dx (get-uav x ens))
                    (uav->dx (get-uav i ens))
                    )))
       :hints (("Goal" :in-theory (enable get-uav-ensemble-index-congruence)
                :induct (escort-right-index i ens))
               (stable-p :in-theory (ensemble-index-equiv-theory))))
       

     (defthmd included-in-escort-right-index
       (implies
        (and
         (<= (ensemble-index x ens) (escort-right-index i ens))
         (<= (ensemble-index i ens) (ensemble-index x ens)))
        (and (equal (uav->xx (get-uav x ens))
                    (uav->xx (get-uav i ens))
                    )
             (equal (uav->dx (get-uav x ens))
                    (uav->dx (get-uav i ens))
                    )))
       :hints (("Goal" :use (:instance included-in-escort-right-index-helper
                                       (x (ensemble-index x ens))))))
            
     (local (include-arithmetic)) ;; book "arithmetic-5/top" :dir :system))
     
     (defthmd within-escort-group-p-implies-equal-escort-left-index-1-helper
       (implies
        (and
         (<= (ESCORT-LEFT-INDEX x ENS) (nfix i))
         (<= (nfix i) (ensemble-index x ens)))
        (equal (ESCORT-LEFT-INDEX i ENS)
               (ESCORT-LEFT-INDEX X ENS)))
       :hints (("Goal"  :in-theory (enable escort-left-index-ensemble-index-equiv
                                           get-uav-ensemble-index-congruence)
                :induct (ESCORT-LEFT-INDEX X ENS))))

     (defthmd within-escort-group-p-implies-equal-escort-left-index-1
       (implies
        (and
         (<= (ESCORT-LEFT-INDEX x ENS) (ensemble-index i ens))
         (<= (ensemble-index i ens) (ensemble-index x ens)))
        (equal (ESCORT-LEFT-INDEX i ENS)
               (ESCORT-LEFT-INDEX X ENS)))
       :hints (("Goal"  :use (:instance within-escort-group-p-implies-equal-escort-left-index-1-helper
                                        (i (ensemble-index i ens))))))

     (defthmd within-escort-group-p-implies-equal-escort-right-index-1-helper
       (implies
        (and
         (<= (ensemble-index x ens) (nfix i))
         (<= (nfix i) (ESCORT-RIGHT-INDEX x ENS)))
        (equal (ESCORT-RIGHT-INDEX i ENS)
               (ESCORT-RIGHT-INDEX X ENS)))
       :hints (("Goal" :in-theory (enable escort-right-index-ensemble-index-equiv
                                          get-uav-ensemble-index-congruence)
                :induct (ESCORT-RIGHT-INDEX x ENS))))
     
     (defthmd within-escort-group-p-implies-equal-escort-right-index-1
       (implies
        (and
         (<= (ensemble-index x ens) (ensemble-index i ens))
         (<= (ensemble-index i ens) (ESCORT-RIGHT-INDEX x ENS)))
        (equal (ESCORT-RIGHT-INDEX i ENS)
               (ESCORT-RIGHT-INDEX X ENS)))
       :hints (("Goal" :use (:instance within-escort-group-p-implies-equal-escort-right-index-1-helper
                                       (i (ensemble-index i ens))))))
     
     (defthmd within-escort-group-p-implies-equal-escort-left-index-2-helper
       (implies
        (and
         (<= (ensemble-index x ens) (nfix i))
         (<= (nfix i) (ESCORT-RIGHT-INDEX x ENS)))
        (equal (ESCORT-LEFT-INDEX i ENS)
               (ESCORT-LEFT-INDEX X ENS)))
       :hints (("Goal" :in-theory (enable escort-left-index-ensemble-index-equiv
                                          get-uav-ensemble-index-congruence)
                :induct (ESCORT-RIGHT-INDEX x ENS))
               (stable-p :in-theory (ensemble-index-equiv-theory))))
     

     (defthmd within-escort-group-p-implies-equal-escort-left-index-2
       (implies
        (and
         (<= (ensemble-index x ens) (ensemble-index i ens))
         (<= (ensemble-index i ens) (ESCORT-RIGHT-INDEX x ENS)))
        (equal (ESCORT-LEFT-INDEX i ENS)
               (ESCORT-LEFT-INDEX X ENS)))
       :hints (("Goal" :use (:instance within-escort-group-p-implies-equal-escort-left-index-2-helper
                                       (i (ensemble-index i ens))))))
                             
     (defthmd within-escort-group-p-implies-equal-escort-right-index-2-helper
       (implies
        (and
         (<= (ESCORT-LEFT-INDEX x ENS) (nfix i))
         (<= (nfix i) (ensemble-index x ens)))
        (equal (ESCORT-RIGHT-INDEX i ENS)
               (ESCORT-RIGHT-INDEX X ENS)))
       :hints (("Goal" :in-theory (enable escort-right-index-ensemble-index-equiv
                                          get-uav-ensemble-index-congruence)
                :induct (ESCORT-LEFT-INDEX x ENS))
               (stable-p :in-theory (ensemble-index-equiv-theory)
                         :expand (ESCORT-RIGHT-INDEX X ENS))))

     (defthmd within-escort-group-p-implies-equal-escort-right-index-2
       (implies
        (and
         (<= (ESCORT-LEFT-INDEX x ENS) (ensemble-index i ens))
         (<= (ensemble-index i ens) (ensemble-index x ens)))
        (equal (ESCORT-RIGHT-INDEX i ENS)
               (ESCORT-RIGHT-INDEX X ENS)))
       :hints (("Goal" :use (:instance within-escort-group-p-implies-equal-escort-right-index-2-helper
                                       (i (ensemble-index i ens))))))
                                  
     ))

  (local (in-theory (disable STRICTLY-LESS-MEANS-REDUCE-1
                             STRICTLY-LESS-MEANS-REDUCE-2)))
  
  (defthm within-escort-group-fundamental-properties-1
    (implies
     (within-escort-group-p i x ens)
     (and (equal (current-location i ens)
                 (current-location x ens))
          (iff (left-moving-p i ens)
               (left-moving-p x ens))))
    :otf-flg t
    :hints (("goal" :do-not-induct t
             :in-theory (enable left-moving-p current-location
                                included-in-escort-right-index
                                included-in-escort-left-index)
             :cases ((< (ensemble-index i ens) (ensemble-index x ens)))
             )))

  (defthm within-escort-group-fundamental-properties-2
    (implies
     (within-escort-group-p i x ens)
     (and (equal (ESCORT-LEFT-INDEX i ENS)
                 (ESCORT-LEFT-INDEX X ENS))
          (equal (ESCORT-RIGHT-INDEX i ENS)
                 (ESCORT-RIGHT-INDEX X ENS))
          ))
    :hints (("goal" :do-not-induct t
             :in-theory (enable left-moving-p current-location
                                within-escort-group-p-implies-equal-escort-right-index-1
                                within-escort-group-p-implies-equal-escort-right-index-2
                                within-escort-group-p-implies-equal-escort-left-index-1
                                within-escort-group-p-implies-equal-escort-left-index-2
                                )
             :cases ((< (ensemble-index i ens) (ensemble-index x ens)))
             )))
  
  (local
   (defthm uav->xx-get-uav
     (equal (UAV->XX (GET-UAV I ENS))
            (current-location i ens))
     :hints (("Goal" :in-theory (enable current-location)))))

  (local
   (defthm uav->dx-get-uav
     (equal (equal (UAV->DX (get-uav x ens)) 1)
            (not (left-moving-p x ens)))
     :hints (("Goal" :in-theory (enable left-moving-p)))))

  (defthm equal-sign-reduction
    (implies
     (and (sign-p x) (syntaxp (and (not (quotep x)) (not (quotep y)))))
     (iff (equal x y)
          (and (sign-p y)
               (or (and (equal x -1)
                        (equal y -1))
                   (and (equal x 1)
                        (equal y 1)))))))

  (defthm within-escort-group-fundamental-properties-3
    (implies
     (within-escort-group-p i x ens)
     (and (equal (ESCORT->xx (get-escort i ens))
                 (ESCORT->xx (get-escort x ens)))
          (equal (ESCORT->dx (get-escort i ens))
                 (ESCORT->dx (get-escort x ens)))))
    :hints (("Goal" :in-theory (e/d (get-escort) (SIMPLE-WITHIN-ESCORT-GROUP)))))
            
  (defthm within-escort-group-fundamental-properties-4
    (implies
     (within-escort-group-p i x ens)
     (and (equal (ESCORT->LI (GET-ESCORT I ENS))
                 (ESCORT->LI (GET-ESCORT x ENS)))
          (equal (ESCORT->RI (GET-ESCORT I ENS))
                 (ESCORT->RI (GET-ESCORT x ENS)))))
    :hints (("Goal" :in-theory (e/d (get-escort) (SIMPLE-WITHIN-ESCORT-GROUP)))))

  (defthm escort->li-upper-bound
    (<= (ESCORT->LI (GET-ESCORT I ENS)) (ENSEMBLE-INDEX I ENS))
    :rule-classes (:linear))
  
  )

(in-theory (disable SIMPLE-WITHIN-ESCORT-GROUP get-uav get-escort))

(defthm within-escort-group-immediate-properties
  (implies
   (within-escort-group-p i x ens)
   (equal (meta-left-escort-count i ens)
          (- (meta-left-escort-count x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :hints (("Goal" :do-not-induct t)))

;; (def::un escort-group-invariant-property-p (i x ens)
;;   (declare (xargs :guard t :congruence ((nat-equiv nat-equiv ens-equiv) equal)))
;;   (let ((i (nfix i))
;;         (x (nfix x))
;;         (ens (ens-fix ens)))
;;     (and (equal (LeftPerimeterGuess i ens)
;;                 (LeftPerimeterGuess x ens))
;;          (equal (RightPerimeterGuess i ens)
;;                 (RightPerimeterGuess x ens))
;;          (implies
;;           (< x i)
;;           (< (- i x) (LeftCountGuess x ens)))
;;          (equal (LeftCountGuess i ens)
;;                 (- (LeftCountGuess x ens) (- x i)))
;;          (implies
;;           (< i x)
;;           (< (- x i) (RightCountGuess x ens)))
;;          (equal (RightCountGuess i ens)
;;                 (+ (RightCountGuess x ens) (- x i))))))

;; (defun-sk escort-group-invariant-p (x ens)
;;   (declare (xargs :guard t))
;;   (forall (i)
;;     (implies
;;      (and (<= (nfix i) (ESCORT-RIGHT-INDEX (nfix x) (ens-fix ENS)))
;;           (<= (ESCORT-LEFT-INDEX (nfix x) (ens-fix ENS)) (nfix i)))
;;      (escort-group-invariant-property-p i x ens)))
;;   :strengthen t)

;; (encapsulate
;;     ()

;;   (local (in-theory (disable escort-group-invariant-property-p)))

;;   (quant::congruence escort-group-invariant-p (x ens)
;;     (forall (i)
;;       (implies
;;        (and (<= (nfix i) (ESCORT-RIGHT-INDEX (nfix x) ENS))
;;             (<= (ESCORT-LEFT-INDEX (nfix x) ENS) (nfix i)))
;;        (escort-group-invariant-property-p i x ens)))
;;     :congruences ((x nat-equiv)
;;                   (ens ens-equiv)))

;;   )


(encapsulate
    (
     ;;((lc-max)       => *)
     ((max-index)       => *)
     ((ActualLeftPerimeter)           => *)
     ((ActualRightPerimeter)           => *)
     )

  (local
   (encapsulate
       ()
     (set-irrelevant-formals-ok t)
     (set-ignore-ok t)
     
     ;(defun ens-assumption (ens) nil)
       
     (defun max-index () 10)
     (defun ActualLeftPerimeter () 0)
     (defun ActualRightPerimeter () 1)
     ;;(defun lc-max () 0)
     ))
  
  #+joe
  (defthm integerp-lc-max
    (integerp  (lc-max))
    :rule-classes (:type-prescription))
  
  (defthm integerp-max-index
    (integerp  (max-index))
    :rule-classes (:type-prescription))

  (defthm rationalp-ActualLeftPerimeter
    (rationalp (ActualLeftPerimeter))
    :rule-classes :type-prescription)
  
  (defthm rationalp-RightPerimeter
    (rationalp (ActualRightPerimeter))
    :rule-classes :type-prescription)

  (defthm positive-max-index
    (<= 1 (max-index))
    :rule-classes ((:forward-chaining :trigger-terms ((max-index)))))
  
  #+joe
  (defthm lc-max-upper-bound
    (<= (lc-max) (max-index))
    :rule-classes ((:forward-chaining :trigger-terms ((lc-max) (max-index)))))

  (defthm perimeter-boundaries
    (< (ActualLeftPerimeter) (ActualRightPerimeter))
    :rule-classes ((:forward-chaining :trigger-terms ((ActualLeftPerimeter) (ActualRightPerimeter)))))
    
  )

(def::un left-coordinated-pair-p (i x ens)
  (declare (xargs :fty ((nat nat ens) bool)))
  (and (equal (LeftPerimeterGuess i ens)
              (LeftPerimeterGuess x ens))
       (implies
        (<= (ensemble-index i ens) (ensemble-index x ens))
        (<= 0 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
       (equal (LeftCountGuess i ens)
              (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))

(defthm left-coordinated-pair-p-ensemble-index
  (and (equal (left-coordinated-pair-p i (ensemble-index x ens) ens)
              (left-coordinated-pair-p i x ens))
       (equal (left-coordinated-pair-p (ensemble-index i ens) x ens)
              (left-coordinated-pair-p i x ens))))

(def::un co-located-left-coordinated-p (i x ens)
  (declare (xargs :fty ((nat nat ens) bool)))
  (implies
   (and
    (equal (left-moving-p i ens)
           (left-moving-p x ens))
    (equal (current-location i ens)
           (current-location x ens)))
   (left-coordinated-pair-p i x ens)))

;; (and (equal (LeftPerimeterGuess i ens)
;;             (LeftPerimeterGuess x ens))
;;      (implies
;;       (<= (ensemble-index i ens) (ensemble-index x ens))
;;       (<= 0 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
;;      (equal (LeftCountGuess i ens)
;;             (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))))

(def::un right-coordinated-pair-p (i x ens)
  (declare (xargs :fty ((nat nat ens) bool)))
  (and (equal (RightPerimeterGuess i ens)
              (RightPerimeterGuess x ens))
       (implies
        (<= (ensemble-index x ens) (ensemble-index i ens))
        (<= 0 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
       (equal (RightCountGuess i ens)
              (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))

(defthm right-coordinated-pair-p-ensemble-index
  (and (equal (right-coordinated-pair-p i (ensemble-index x ens) ens)
              (right-coordinated-pair-p i x ens))
       (equal (right-coordinated-pair-p (ensemble-index i ens) x ens)
              (right-coordinated-pair-p i x ens))))

(def::un co-located-right-coordinated-p (i x ens)
  (declare (xargs :fty ((nat nat ens) bool)))
  (implies
   (and
    (equal (left-moving-p i ens)
           (left-moving-p x ens))
    (equal (current-location i ens)
           (current-location x ens)))
   (right-coordinated-pair-p i x ens)))


;; (and (equal (RightPerimeterGuess i ens)
;;             (RightPerimeterGuess x ens))
;;      (implies
;;       (<= (ensemble-index x ens) (ensemble-index i ens))
;;       (<= 0 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
;;      (equal (RightCountGuess i ens)
;;             (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))

;; Left-coordinated escort invariant

(defun-sk all-within-escort-left-coordinated-p (ens)
  (declare (xargs :guard t))
  (forall (i x)
    (co-located-left-coordinated-p (nfix i) (nfix x) (ens-fix ens)))
  :strengthen t)

(in-theory (disable all-within-escort-left-coordinated-p))

(encapsulate
    ()

  (local (in-theory (disable co-located-left-coordinated-p)))
  
  (quant::congruence all-within-escort-left-coordinated-p (ens)
    (forall (i x)
      (co-located-left-coordinated-p (nfix i) (nfix x) ens))
    :congruences ((ens ens-equiv)))

  )
  
(defthmd all-within-escort-left-coordinated-p-consequence
  (implies
   (and
    (all-within-escort-left-coordinated-p ens)
    (equal (left-moving-p i ens)
           (left-moving-p x ens))
    (equal (current-location i ens)
           (current-location x ens)))
   (and (equal (LeftPerimeterGuess i ens)
               (LeftPerimeterGuess x ens))
        (implies
         (<= (ensemble-index i ens) (ensemble-index x ens))
         (<= 0 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
        (equal (LeftCountGuess i ens)
               (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("Goal" :use all-within-escort-left-coordinated-p-necc)))

(defun-sk all-within-escort-right-coordinated-p (ens)
  (declare (xargs :guard t))
  (forall (i x)
    (co-located-right-coordinated-p (nfix i) (nfix x) (ens-fix ens)))
  :strengthen t)

(in-theory (disable all-within-escort-right-coordinated-p))

(encapsulate
    ()

  (local (in-theory (disable co-located-right-coordinated-p)))
  
  (quant::congruence all-within-escort-right-coordinated-p (ens)
    (forall (i x)
      (co-located-right-coordinated-p (nfix i) (nfix x) ens))
    :congruences ((ens ens-equiv)))

  )
  
(defthmd all-within-escort-right-coordinated-p-consequence
  (implies
   (and
    (all-within-escort-right-coordinated-p ens)
    (equal (left-moving-p i ens)
           (left-moving-p x ens))
    ;;(syntaxp (good-rewrite-order i x))
    (equal (current-location i ens)
           (current-location x ens)))
   (and (equal (RightPerimeterGuess i ens)
               (RightPerimeterGuess x ens))
        (implies
         (<= (ensemble-index x ens) (ensemble-index i ens))
         (<= 0 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
        (equal (RightCountGuess i ens)
               (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("Goal" :use all-within-escort-right-coordinated-p-necc)))

(defun-sk all-ordered-locations (ens)
  (declare (xargs :guard t))
  (forall (i)
    (<= (current-location (+ -1 (ensemble-index i ens)) ens)
        (current-location i ens)))
  :strengthen t)

(quant::congruence all-ordered-locations (ens)
  (forall (i)
    (<= (current-location (+ -1 (ensemble-index i ens)) ens)
        (current-location i ens)))
  :congruences ((ens ens-equiv)))

(in-theory (disable all-ordered-locations))

(defthmd all-ordered-locations-implication
  (implies
   (all-ordered-locations ens)
   (<= (current-location (+ -1 (ensemble-index i ens)) ens)
       (current-location i ens)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not-induct t
           :use all-ordered-locations-necc)))
    
(encapsulate
    ()

  ;;(local (in-theory (enable current-location-order-instance)))
  (local (in-theory (enable all-ordered-locations-implication)))
  
  (local
   (encapsulate
       ()
     
     (defun what-it-means (lower upper ens)
       (declare (xargs :measure (nfix (- (ensemble-index upper ens) (ensemble-index lower ens)))))
       (if (<= (ensemble-index upper ens) (ensemble-index lower ens)) t
         (and (<= (current-location (1- (ensemble-index upper ens)) ens) (current-location upper ens))
              (what-it-means lower (1- (ensemble-index upper ens)) ens))))
     
     (defthm consequence
       (implies
        (and
         (what-it-means x y ens)
         (<= (ensemble-index x ens) (ensemble-index y ens)))
        (<= (current-location x ens) (current-location y ens))))
     
     (defthm what-it-means-is-true
       (implies
        (all-ordered-locations ens)
        (what-it-means x y ens))
       :hints (("Goal" :induct (what-it-means x y ens))))
     
     ))
  
  (def::linear current-location-order
    (implies
     (and
      (syntaxp (not (equal x y)))
      (all-ordered-locations ens)
      (<= (ensemble-index x ens) (ensemble-index y ens)))
     (<= (current-location x ens) (current-location y ens))))
  
  )

;; (def::linear current-location-order-ensemble-index
;;   (implies
;;    (and
;;     (syntaxp (not (equal i j)))
;;     (all-ordered-locations ens)
;;     (<= (ensemble-index i ens)
;;         (ensemble-index j ens)))
;;    (<= (current-location i ens)
;;        (current-location j ens)))
;;   :hints (("Goal" :in-theory (e/d (current-location-ensemble-index!)
;;                                   (current-location-ensemble-index)))))

(defthmd all-ordered-locations-pinching-lemma
  (implies
   (and
    (all-ordered-locations ens)
    (<= (ensemble-index i ens) (ensemble-index j ens))
    (<= (ensemble-index j ens) (ensemble-index k ens))
    (equal (current-location i ens)
           (current-location k ens)))
   (equal (current-location j ens)
          (current-location k ens))))

(defthm escort-agree-on-left-coordination-variables
  (implies
   (and
    (within-escort-group-p i x ens)
    (all-within-escort-left-coordinated-p ens))
   (and (equal (LeftPerimeterGuess i ens)
               (LeftPerimeterGuess x ens))
        (equal (LeftCountGuess i ens)
               (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("Goal" :use (:instance all-within-escort-left-coordinated-p-consequence))))

(defthm escort-agree-on-left-coordination-variables-linear
  (implies
   (and
    (within-escort-group-p i x ens)
    (<= (ensemble-index i ens) (ensemble-index x ens))
    (all-within-escort-left-coordinated-p ens))
   (<= 0 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :rule-classes ((:linear :trigger-terms ((LeftCountGuess x ens))))
  :hints (("Goal" :use (:instance all-within-escort-left-coordinated-p-consequence))))

(defthm escort-agree-on-right-coordination-variables
  (implies
   (and
    (within-escort-group-p i x ens)
    (all-within-escort-right-coordinated-p ens))
   (and (equal (RightPerimeterGuess i ens)
               (RightPerimeterGuess x ens))
        (equal (RightCountGuess i ens)
               (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("Goal" :use (:instance all-within-escort-right-coordinated-p-consequence))))

(defthm escort-agree-on-right-coordination-variables-linear
  (implies
   (and
    (within-escort-group-p i x ens)
    (<= (ensemble-index x ens) (ensemble-index i ens))
    (all-within-escort-right-coordinated-p ens))
   (<= 0 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :rule-classes ((:linear :trigger-terms ((RightCountGuess x ens))))
  :hints (("Goal" :use (:instance all-within-escort-right-coordinated-p-consequence))))

(def::un current-location-bounds-p (x ens)
  (declare (xargs :signature ((t t) booleanp)
                  :congruence ((nat-equiv ens-equiv) equal)))
  (let ((x (nfix x)))
    (and
     (<= (ActualLeftPerimeter)
         (current-location x ens))
     (<= (current-location x ens)
         (ActualRightPerimeter)))))

(defun-sk all-current-locations-bounded-p (ens)
  (declare (xargs :guard t))
  (forall (x) (current-location-bounds-p x ens))
  :strengthen t)

(in-theory (disable all-current-locations-bounded-p))

(encapsulate
    ()

  (local (in-theory (disable current-location-bounds-p)))

  (quant::congruence all-current-locations-bounded-p (ens)
    (forall (x) (current-location-bounds-p x ens))
    :congruences ((ens ens-equiv)))

  )
  
(defthm all-current-locations-bounded-p-implication
  (implies
   (all-current-locations-bounded-p ens)
   (and (<= (ActualLeftPerimeter)
            (current-location x ens))
        (<= (current-location x ens)
            (ActualRightPerimeter))))
  :hints (("Goal" :use all-current-locations-bounded-p-necc))
  :rule-classes (:linear))
          
(defun-sk all-uavs (ens)
  (declare (xargs :guard t))
  (forall (i) (uav-p (nth (ensemble-index i ens) (list-fix ens))))
  :strengthen t)

(quant::congruence all-uavs (ens)
  (forall (i) (uav-p (nth (ensemble-index i ens) (list-fix ens))))
  :congruences ((ens ens-equiv)))

(in-theory (disable all-uavs))

(defthm all-uavs-consequence
  (implies
   (all-uavs ens)
   (uav-p (nth (ensemble-index i ens) ens)))
  :hints (("Goal" :use all-uavs-necc)))

(defthm all-uavs-set-uav
  (implies
   (and
    (all-uavs ens)
    (consp (DOUBLE-REWRITE ENS)))
   (all-uavs (set-uav i uav ens)))
  :hints (("Goal" :expand (all-uavs (set-uav i uav ens)))
          (stable-p :in-theory (enable set-uav))))

(def::un uav-state-p (ens)
  (declare (xargs :guard t
                  :congruence ((ens-equiv) equal)))
  (and (consp ens)
       (all-uavs ens)
       (all-ordered-locations ens)
       (all-current-locations-bounded-p ens)
       (all-within-escort-left-coordinated-p ens)
       (all-within-escort-right-coordinated-p ens)))

(defthm uav-state-p-implies
  (implies
   (uav-state-p ens)
   (and (consp ens)
        (all-uavs ens)
        (all-ordered-locations ens)
        (all-current-locations-bounded-p ens)
        (all-within-escort-left-coordinated-p ens)
        (all-within-escort-right-coordinated-p ens)))
  :rule-classes (:forward-chaining))
   
(def::und uav-witness ()
  (declare (xargs :signature (() uav-p)))
  (UAV! :LP (ActualLeftPerimeter)
        :LC 0
        :xx (average (ActualLeftPerimeter) (ActualRightPerimeter))
        :dx 1
        :RC 0
        :RP (ActualRightPerimeter)))

(in-theory (disable (uav-witness)))

(defun uav-state-witness ()
  (declare (xargs :guard t))
  (ens-fix (list (uav-witness))))

(defthm all-uavs-uav-state-witness
  (all-uavs (uav-state-witness))
  :hints (("Goal" :in-theory (enable all-uavs))))

(defthm ens-fix-uav-state-witness
  (equal (ens-fix (uav-state-witness))
         (uav-state-witness)))

(defthm len-uav-state-witness
  (equal (len (uav-state-witness)) 1))

(in-theory (disable (uav-state-witness)))

(defthm get-uav-uavs-state-witness
  (equal (get-uav i (uav-state-witness))
         (uav-witness))
  :hints (("Goal" :in-theory (enable ENSEMBLE-INDEX get-uav))))

(defthm consp-uav-state-witness
  (consp (uav-state-witness))
  :hints (("Goal" :in-theory (enable uav-state-witness))))

(in-theory (disable uav-state-witness))

(defthm uav-state-p-uav-state-witness
  (uav-state-p (uav-state-witness))
  :hints (("Goal" :in-theory (enable uav-state-p
                                     average
                                     current-location
                                     uav-witness
                                     ensemble-index
                                     LEFTCOUNTGUESS
                                     LEFTPERIMETERGUESS
                                     RIGHTPERIMETERGUESS
                                     RIGHTCOUNTGUESS
                                     LEFT-MOVING-P
                                     ALL-WITHIN-ESCORT-RIGHT-COORDINATED-P
                                     ALL-WITHIN-ESCORT-LEFT-COORDINATED-P
                                     ALL-CURRENT-LOCATIONS-BOUNDED-P
                                     ALL-ORDERED-LOCATIONS))))

(in-theory (disable uav-state-p))

(def::und uav-state-fix (ens)
  (declare (xargs :signature ((t) uav-state-p)
                  :congruence ((ens-equiv) equal)))
  (if (uav-state-p ens) (ens-fix ens) (uav-state-witness)))

(defthm uav-state-p-implies-uav-state-fix-reduction
  (implies
   (uav-state-p ens)
   (equal (uav-state-fix ens)
          (ens-fix ens)))
  :hints (("Goal" :in-theory (enable uav-state-fix))))

(defun uav-state-equiv (x y)
  (declare (xargs :guard t))
  (ens-equiv (uav-state-fix x)
             (uav-state-fix y)))

(defequiv uav-state-equiv)

(defrefinement ens-equiv uav-state-equiv)

(defcong uav-state-equiv equal (uav-state-fix ens) 1
  :hints (("Goal" :in-theory (enable uav-state-fix uav-state-equiv ))))

(defthm uav-state-equiv-uav-state-fix
  (uav-state-equiv (uav-state-fix x) x))

(in-theory (disable uav-state-equiv))

(def::type-fty uav-state
  :type-p uav-state-p
  :fix    uav-state-fix
  :fix!   uav-state-fix
  :equiv  uav-state-equiv
  :fix-constants nil)

;;
;; move
;; coordinate
;; flip
;;

(def::un pre-move-invariant-p (i j ens)
  (declare (xargs :guard t :congruence ((nat-equiv nat-equiv ens-equiv) equal)))
  (let ((i (ensemble-index i ens))
        (j (ensemble-index j ens))
        (ens (ens-fix ens)))
    (implies
     (equal (current-location i ens)
            (current-location j ens))
     (and
      (not (and (right-moving-p i ens)
                (left-moving-p j ens)))
      (implies
       (and
        (right-moving-p i ens)
        (right-moving-p j ens))
       (<= (current-location i ens) (right-moving-uav-split-location i ens)))
      (implies
       (and
        (left-moving-p i ens)
        (left-moving-p j ens))
       (<= (left-moving-uav-split-location j ens) (current-location i ens)))))))

(defun-sk pre-move-invariant (ens)
  (declare (xargs :guard t))
  (forall (i j) (implies (< (ensemble-index i ens) (ensemble-index j ens)) (pre-move-invariant-p i j ens)))
  :strengthen t)

(in-theory (disable pre-move-invariant))
    
(defthmd pre-move-invariant-implication
  (implies
   (and
    (pre-move-invariant ens)
    (equal (current-location i ens)
           (current-location j ens)))
   (and
    (implies
     (< (ensemble-index i ens) (ensemble-index j ens))
     (pre-move-invariant-p i j ens))
    (implies
     (< (ensemble-index j ens) (ensemble-index i ens))
     (pre-move-invariant-p j i ens))))
  :hints ((pattern-hint
           (< (ensemble-index i ens) (ensemble-index j ens))
           :use ((:instance pre-move-invariant-necc
                            (i i)
                            (j j))))))

(encapsulate
    ()

  (local (in-theory (disable pre-move-invariant-p)))
  
  (quant::congruence pre-move-invariant (ens)
    (forall (i j) (implies (< (ensemble-index i ens) (ensemble-index j ens)) (pre-move-invariant-p i j ens)))
    :congruences ((ens ens-equiv)))

  )

(defthmd leftcountguess-co-located-linear
  (implies
   (and
    (uav-state-p ens)
    (EQUAL (CURRENT-LOCATION I ENS)
           (CURRENT-LOCATION X ENS))
    (EQUAL (LEFT-MOVING-P I ENS)
           (LEFT-MOVING-P X ENS)))
   (EQUAL (LEFTCOUNTGUESS I ENS)
          (- (LEFTCOUNTGUESS X ENS)
             (- (ENSEMBLE-INDEX X ENS)
                (ENSEMBLE-INDEX I ENS)))))
  :hints (("Goal" :use (:instance all-within-escort-left-coordinated-p-consequence)))
  :rule-classes (:linear))

(defthmd rightcountguess-co-located-linear
  (implies
   (and
    (uav-state-p ens)
    (EQUAL (CURRENT-LOCATION I ENS)
           (CURRENT-LOCATION X ENS))
    (EQUAL (LEFT-MOVING-P I ENS)
           (LEFT-MOVING-P X ENS)))
   (equal (RightCountGuess i ens)
          (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :hints (("Goal" :use (:instance all-within-escort-right-coordinated-p-consequence)))
  :rule-classes (:linear))

(defthm test
  (implies
   (uav-state-p ens)
   (and (<= (ActualLeftPerimeter)
            (current-location x ens))
        (<= (current-location x ens)
            (ActualRightPerimeter))
        (implies
         (<= (ensemble-index x ens) (ensemble-index y ens))
         (<= (current-location x ens) (current-location y ens)))
        (implies
         (and
          (equal (current-location i ens) (current-location x ens))
          (or
           (equal (left-moving-p i ens) (left-moving-p x ens))
           ;;(equal phase :coordinate)
           )
          )
         (and
          (equal (LeftPerimeterGuess i ens)
                 (LeftPerimeterGuess x ens))
          (equal (LeftCountGuess i ens)
                 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))
          (equal (RightPerimeterGuess i ens)
                 (RightPerimeterGuess x ens))
          (equal (RightCountGuess i ens)
                 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
        ;; #+joe
        ;; (implies
        ;;  (within-escort-group-p i x ens)
        ;;  (and
        ;;   (equal (current-location i ens) (current-location x ens))
        ;;   (equal (left-moving-p i ens) (left-moving-p x ens))
        ;;   ;; and everything that comes with this .
          ))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable all-within-escort-right-coordinated-p-consequence)
                            :restrict ((all-within-escort-right-coordinated-p-consequence
                                        ((i i) (x x))))))
          (and stable-under-simplificationp
               '(:in-theory (enable all-within-escort-left-coordinated-p-consequence)
                            :restrict ((all-within-escort-left-coordinated-p-consequence
                                        ((i i) (x x))))))
          )
  :rule-classes nil)

(encapsulate

    ()

  (local
   (encapsulate
       ()
     
     (defthm nth-out-of-range
       (implies
        (<= (len y) (nfix i))
        (equal (nth i y) nil))
       :hints (("Goal" :in-theory (enable nth))))
     
     (defthm nth-equiv-to-get-uav-equiv
       (implies
        (and
         (len-equiv x y)
         (all-uavs x)
         (all-uavs y))
        (iff (nth-equiv x y)
             (get-uav-equiv x y)))
       :hints (("Subgoal 1" :in-theory (enable get-uav-equiv
                                               get-uav))
               ("Subgoal 2" :in-theory (e/d (get-uav nth-equiv)
                                            (LEN-EQUIV-2-IMPLIES-EQUAL-ENSEMBLE-INDEX
                                             LEN-EQUIV-IMPLIES-EQUAL-MAX-ENS-INDEX-1
                                             GET-UAV-EQUIV-IMPLIES-EQUAL-GET-UAV-2)))
               (pattern-hint
                (:term (nth i x))
                :limit 1
                :use ((:instance get-uav-equiv-implication
                                 (i i))))
               (stable-p :in-theory (enable LEN-EQUIV-2-IMPLIES-EQUAL-ENSEMBLE-INDEX))
               (stable-p :in-theory (enable ENSEMBLE-INDEX))
               (stable-p :cases ((<= (len x) (NFIX (NTH-EQUIV-WITNESS X Y)))))
               ))
     
     (defthmd equal-to-get-uav-equiv-end
       (implies
        (and
         (all-uavs x)
         (all-uavs y))
        (iff (equal x y)
             (and (end-equiv x y)
                  (len-equiv x y)
                  (get-uav-equiv x y))))
       :hints (("Goal" :use equal-to-nth-equiv-reduction)))
     
     (defthm end-equiv-set-uav
       (implies
        (ens-p ens)
        (end-equiv ens nil)))

     ))
     
  (defthmd equal-to-get-uav-equiv
    (implies
     (and
      (ens-p x)
      (ens-p y)
      (all-uavs x)
      (all-uavs y))
     (iff (equal x y)
          (and (len-equiv x y)
               (get-uav-equiv x y))))
    :hints (("Goal" :use equal-to-get-uav-equiv-end)))

  )
