;;
;; Copyright (C) 2018, Rockwell Collins
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;;
(in-package "ACL2")
(include-book "coi/quantification/quantification" :dir :system)
(include-book "coi/util/deffix" :dir :system)
(include-book "coi/util/good-rewrite-order" :dir :system)

(include-book "env-type")
(include-book "varid-type")

(in-theory (disable remove-non-member))

;; ------------------------------------------------------------------

(set-tau-auto-mode nil)
(def::und default-coeff ()
  (declare (xargs :signature (() rationalp)))
  0)
(set-tau-auto-mode t)

(in-theory (disable (:type-prescription default-coeff) (default-coeff)))

;; ------------------------------------------------------------------

(fty::defprod pair
  ((varid varid-p :rule-classes (:type-prescription :rewrite (:forward-chaining :trigger-terms ((pair->varid x)))))
   (coeff rationalp :rule-classes (:type-prescription :rewrite (:forward-chaining :trigger-terms ((pair->varid x)))))
   ))

(def::un default-pair (varid)
  (declare (xargs :signature ((varid-p) pair-p)))
  (pair varid 0))

(def::un pair-fix! (x)
  (declare (xargs :signature ((t) pair-p)))
  (with-guard-checking :none (ec-call (pair-fix x))))

(defthmd pair-equiv-extensionality
  (iff (pair-equiv x y)
       (and (varid-equiv (pair->varid x)
                         (pair->varid y))
            (rational-equiv (pair->coeff x)
                            (pair->coeff y))))
  :hints (("Goal" :in-theory (enable pair-fix-redef))))

(defthm equal-pair-fix-to-pair-equiv
  (iff (equal (pair-fix x) y)
       (and (pair-p y)
            (pair-equiv x y))))

(in-theory (disable pair-equiv$inline))

(theory-invariant (incompatible (:definition pair-equiv$inline)
                                (:rewrite equal-pair-fix-to-pair-equiv)))

(fty::deflist pair-list
  :elt-type pair-p
  :pred  pair-listp
  :fix   pair-list-fix
  :equiv pair-list-equiv
  :true-listp t
  )

;; (fty::deflist poly
;;   :elt-type pterm-p
;;   :pred poly-p
;;   :fix  poly-type-fix
;;   :equiv pair-list-equiv
;;   :true-listp t
;;   )

(defun pair-list-fix! (x)
  (declare (type t x))
  (with-guard-checking :none (ec-call (pair-list-fix x))))

(defrefinement pair-list-equiv consp-equiv
  :hints (("Goal" :in-theory (enable pair-list-fix))))

(defthm open-pair-list-equiv-on-consp
  (implies
   (consp x)
   (iff (pair-list-equiv x y)
        (and (consp y)
             (equal (pair-fix (car x)) (pair-fix (car y)))
             (pair-list-equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable pair-list-fix))))

(defthm open-pair-list-equiv-on-not-consp
  (implies
   (not (consp x))
   (iff (pair-list-equiv x y)
        (not (consp y))))
  :hints (("Goal" :in-theory (enable pair-list-fix))))

(defthm equal-pair-list-fix-to-pair-list-equiv
  (iff (equal (pair-list-fix x) y)
       (and (pair-listp y)
            (pair-list-equiv x y))))

(in-theory (disable pair-list-equiv$inline))
(theory-invariant (incompatible (:definition pair-list-equiv$inline)
                                (:rewrite equal-pair-list-fix-to-pair-list-equiv)))

;;(in-theory (disable CONS-OF-WF-BINDING-FIX-X-NORMALIZE-CONST-UNDER-ENV-TYPE-EQUIV))

(defthm car-pair-list-fix
  (equal (car (pair-list-fix poly))
         (if (consp poly) (pair-fix (car poly)) nil)))

(defthm cdr-pair-list-fix
  (equal (cdr (pair-list-fix poly))
         (pair-list-fix (cdr poly))))

;; ------------------------------------------------------------

(def::un get-coeff (var poly)
  (declare (xargs :signature ((t t) rationalp)
                  :congruence ((varid-equiv pair-list-equiv) equal)
                  :measure (len poly)))
  (let ((var  (varid-fix var)))
    (if (not (consp poly)) 0
      (let ((pair (pair-fix! (car poly))))
        (if (varid-equiv var (pair->varid pair))
            (pair->coeff pair)
          (get-coeff var (cdr poly)))))))

;; ----------------------------------------------------------------------------

(def::un-sk pair-list-get-equiv (x y)
  (forall (a) (equal (get-coeff a x)
                     (get-coeff a y))))

(verify-guards pair-list-get-equiv)

(defequiv pair-list-get-equiv
  :hints ((quant::inst?)))

(defcong pair-list-get-equiv equal (get-coeff a x) 2
  :hints ((quant::inst?)))

(encapsulate
 ()

 (encapsulate
  (((pair-list-get-equiv-hyps) => *)
   ((pair-list-get-equiv-left) => *)
   ((pair-list-get-equiv-right) => *))

  (local (defun pair-list-get-equiv-hyps () nil))
  (local (defun pair-list-get-equiv-left () nil))
  (local (defun pair-list-get-equiv-right () nil))

  (defthm pair-list-get-equiv-multiplicity-constraint
    (implies
     (pair-list-get-equiv-hyps)
     (equal (get-coeff arbitrary-varid (pair-list-get-equiv-left))
            (get-coeff arbitrary-varid (pair-list-get-equiv-right))))
    :rule-classes nil)
  )

 (defthm pair-list-get-equiv-by-multiplicity-driver
   (implies (pair-list-get-equiv-hyps)
            (pair-list-get-equiv (pair-list-get-equiv-left) (pair-list-get-equiv-right)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        pair-list-get-equiv-multiplicity-constraint
                        (arbitrary-varid hide)))))))

 (ADVISER::defadvice ADVISER::pair-list-get-equiv-by-multiplicity
   (implies (pair-list-get-equiv-hyps)
            (pair-list-get-equiv (pair-list-get-equiv-left) (pair-list-get-equiv-right)))
   :rule-classes (:pick-a-point :driver pair-list-get-equiv-by-multiplicity-driver))

 )

(in-theory (disable pair-list-get-equiv))

(defthm pair-list-get-equiv-pair-list-fix
  (pair-list-get-equiv (pair-list-fix x) x))

(defrefinement pair-list-equiv pair-list-get-equiv)

(def::fix pair-list-get-fix
  pair-list-get-equiv
  :type      pair-listp
  :type-fix  pair-list-fix
  )

;; ----------------------------------------------------------------------------

(def::un pair-list-keys (poly)
  (declare (xargs :signature ((t) varid-listp)
                  :congruence ((pair-list-equiv) set-equiv-quant)))
  (if (not (consp poly)) nil
    (let ((pair (pair-fix! (car poly))))
      (set-insert (pair->varid pair)
                  (pair-list-keys (cdr poly))))))

(local
 (defthm consp-implies-memberp-car
   (implies
    (consp list)
    (list::memberp (car list) list))
   :rule-classes (:forward-chaining)))

(defthm get-coeff-zero-outside-keys
  (implies
   (not (list::memberp (varid-fix a) (pair-list-keys poly)))
   (equal (get-coeff a poly) 0)))

(defun pair-list-key-equiv (x y)
  (declare (type t x y))
  (set-equiv-quant (pair-list-keys x)
                   (pair-list-keys y)))

(defequiv pair-list-key-equiv)
(defrefinement pair-list-equiv pair-list-key-equiv)
(defcong pair-list-key-equiv set-equiv-quant (pair-list-keys x) 1)

(in-theory (disable pair-list-key-equiv))

;; ----------------------------------------------------------------------------

(defun pair-list-both-equiv (x y)
  (declare (type t x y))
  (and (pair-list-key-equiv x y)
       (pair-list-get-equiv x y)))

(defequiv pair-list-both-equiv)
(defrefinement pair-list-equiv pair-list-both-equiv)
(defrefinement pair-list-both-equiv pair-list-key-equiv)
(defrefinement pair-list-both-equiv pair-list-get-equiv)

(defthm key-get-equiv-implies-both-equiv
  (implies
   (and (pair-list-key-equiv x y)
        (pair-list-get-equiv x y))
   (pair-list-both-equiv x y))
  :rule-classes (:forward-chaining))

;; ----------------------------------------------------------------------------

(def::un drop-varid (varid poly)
  (declare (xargs :signature ((t t) pair-listp)
                  :congruence ((varid-equiv pair-list-equiv) pair-list-equiv)
                  :measure (len poly)))
  (if (not (consp poly)) nil
    (let ((pair (pair-fix! (car poly))))
      (if (varid-equiv varid (pair->varid pair))
          (drop-varid varid (cdr poly))
        (cons pair (drop-varid varid (cdr poly)))))))

(defthm len-drop-varid
  (<= (len (drop-varid varid poly))
      (len poly))
  :rule-classes :linear)

(defthm pair-varid-car-is-memberp
  (implies
   (consp poly)
   (list::memberp (pair->varid (car poly)) (pair-list-keys poly))))

(defthm len-drop-varid-stronger
  (implies
   (list::memberp (varid-fix varid) (pair-list-keys poly))
   (< (len (drop-varid varid poly))
      (len poly)))
  :rule-classes :linear)

(defthm pair-list-keys-drop-varid
  (set-equiv-quant (pair-list-keys (drop-varid varid poly))
                   (remove-equal (varid-fix varid) (pair-list-keys poly))))

(defcong pair-list-key-equiv pair-list-key-equiv (drop-varid varid poly) 2
  :hints (("Goal" :in-theory (enable pair-list-key-equiv))))

(defthm get-coeff-drop-varid
  (equal (get-coeff a (drop-varid b poly))
         (if (varid-equiv a b) 0
           (get-coeff a poly))))

(defcong pair-list-get-equiv pair-list-get-equiv (drop-varid varid poly) 2)

(defcong pair-list-both-equiv pair-list-both-equiv (drop-varid varid poly) 2)

;; ----------------------------------------------------------------------------

(encapsulate
    ()

  (local (in-theory (disable get-coeff-drop-varid PAIR-LIST-GET-EQUIV-IMPLIES-EQUAL-GET-COEFF-2)))

  (defthmd open-pair-list-get-equiv-on-drop-varid
    (iff (pair-list-get-equiv p1 p2)
         (and (equal (get-coeff a p1)
                     (get-coeff a p2))
              (pair-list-get-equiv (drop-varid a p1)
                                   (drop-varid a p2))))
    :hints (("Goal" :do-not-induct t)
            (quant::inst?)
            (and stable-under-simplificationp
                 '(:cases ((varid-equiv a hide))))
            (and stable-under-simplificationp
                 '(:cases ((equal (get-coeff hide (drop-varid a p1))
                                  (get-coeff hide (drop-varid a p2))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable get-coeff-drop-varid)))))

  )

;; ----------------------------------------------------------------------------

(def::un keep-nz-keys (keys poly)
  (declare (xargs :signature ((t t) true-listp)
                  :congruence ((nil pair-list-get-equiv) equal)))
  (if (not (consp keys)) nil
    (let ((varid (car keys)))
      (if (equal (get-coeff varid poly) 0)
          (keep-nz-keys (cdr keys) poly)
        (cons varid (keep-nz-keys (cdr keys) poly))))))

(def::signature keep-nz-keys (varid-listp t) varid-listp)

(defthm memberp-keep-nz-keys
  (iff (list::memberp a (keep-nz-keys keys poly))
       (if (equal (get-coeff a poly) 0) nil
         (list::memberp a keys)))
  :hints (("Goal" :in-theory (enable varid-list-fix)
           :induct (keep-nz-keys keys poly))))

(defcong set-equiv-quant set-equiv-quant (keep-nz-keys keys poly) 1
  :hints (("Goal" :do-not-induct t)))

(def::un pair-list-nz-keys (poly)
  (declare (xargs :signature ((t) varid-listp)
                  :congruence ((pair-list-both-equiv) set-equiv-quant)))
  (keep-nz-keys (pair-list-keys poly) poly))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm non-zeros-are-in-keys
       (implies
        (and
         (not (equal (get-coeff a poly) 0))
         (varid-p a))
        (list::memberp a (PAIR-LIST-KEYS poly)))
       :rule-classes (:forward-chaining :rewrite))

     (defthm equal-boolean-reduction
       (implies
        (booleanp x)
        (iff (equal x y)
             (and (booleanp y)
                  (iff x y)))))

     (defthm varid-p-from-membership
       (implies
        (and
         (list::memberp a list)
         (varid-listp list))
        (varid-p a))
       :rule-classes (:rewrite :forward-chaining)
       :hints (("Goal" :in-theory (enable list::memberp varid-listp))))

     ))

  (defcong pair-list-get-equiv set-equiv-quant (pair-list-nz-keys poly) 1)

  )

(defthmd member-pair-list-nz-keys
  (iff (list::memberp a (pair-list-nz-keys x))
       (and (list::memberp a (pair-list-keys x))
            (not (equal (get-coeff a x) 0)))))

(defthm member-pair-list-nz-keys-implication
  (implies
   (list::memberp a (pair-list-nz-keys x))
   (and (list::memberp a (pair-list-keys x))
        (not (equal (get-coeff a x) 0))))
  :hints (("Goal" :in-theory (enable member-pair-list-nz-keys)))
  :rule-classes (:forward-chaining))

(defthm non-zero-property-of-key-membership
  (implies
   (list::memberp a (pair-list-nz-keys list))
   (not (equal (get-coeff a list) 0))))

(defthm zero-property-of-non-membership
  (implies
   (not (list::memberp (varid-fix a) (pair-list-nz-keys list)))
   (equal (get-coeff a list)
          0)))

(defthm empty-nz-keys-implies-get-coeff-zero
  (implies
   (not (consp (pair-list-nz-keys list)))
   (equal (get-coeff a list)
          0)))

(defun pair-list-nz-key-equiv (x y)
  (declare (type t x y))
  (set-equiv-quant (pair-list-nz-keys x)
                   (pair-list-nz-keys y)))

(defequiv pair-list-nz-key-equiv)

(defrefinement pair-list-both-equiv pair-list-nz-key-equiv)
(defcong pair-list-nz-key-equiv set-equiv-quant (pair-list-nz-keys x) 1)

;; Mihir M. mod Nov. 2020: I disabled a whole bunch of rules that were causing
;; this lemma to fail.
(defrefinement pair-list-get-equiv pair-list-nz-key-equiv
  :rule-classes (:refinement :forward-chaining)
  :hints (("Goal"
           :in-theory (disable
                       (:congruence pair-list-get-equiv-1-implies-equal-keep-nz-keys)
                       (:definition pair-list-nz-keys)
                       (:definition synp)
                       (:meta *meta*-beta-reduce-hide)
                       (:rewrite memberp-keep-nz-keys)
                       (:rewrite set-equiv-quant-by-multiplicity)))))

(encapsulate
 ()

 (encapsulate
  (((pair-list-nz-key-equiv-hyps) => *)
   ((pair-list-nz-key-equiv-left) => *)
   ((pair-list-nz-key-equiv-right) => *))

  (local (defun pair-list-nz-key-equiv-hyps () nil))
  (local (defun pair-list-nz-key-equiv-left () nil))
  (local (defun pair-list-nz-key-equiv-right () nil))

  (defthm pair-list-nz-key-equiv-multiplicity-constraint
    (implies
     (pair-list-nz-key-equiv-hyps)
     (equal (and (list::memberp arbitrary-varid (pair-list-keys (pair-list-nz-key-equiv-left)))
                 (not (equal (get-coeff arbitrary-varid (pair-list-nz-key-equiv-left)) 0)))
            (and (list::memberp arbitrary-varid (pair-list-keys (pair-list-nz-key-equiv-right)))
                 (not (equal (get-coeff arbitrary-varid (pair-list-nz-key-equiv-right)) 0)))))
    :rule-classes nil)
  )


 (local (in-theory (enable member-pair-list-nz-keys)))

 (defthm pair-list-nz-key-equiv-by-multiplicity-driver
   (implies (pair-list-nz-key-equiv-hyps)
            (pair-list-nz-key-equiv (pair-list-nz-key-equiv-left) (pair-list-nz-key-equiv-right)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        pair-list-nz-key-equiv-multiplicity-constraint
                        (arbitrary-varid hide)))))))

 (ADVISER::defadvice ADVISER::pair-list-nz-key-equiv-by-multiplicity
   (implies (pair-list-nz-key-equiv-hyps)
            (pair-list-nz-key-equiv (pair-list-nz-key-equiv-left) (pair-list-nz-key-equiv-right)))
   :rule-classes (:pick-a-point :driver pair-list-nz-key-equiv-by-multiplicity-driver))

 )


(in-theory (disable pair-list-nz-keys))

(encapsulate
    ()

  (local (in-theory (enable member-pair-list-nz-keys)))

  (local
   (defthm varid-p-from-membership
     (implies
      (and
       (list::memberp a list)
       (varid-listp list))
      (varid-p a))
     :hints (("Goal" :in-theory (enable list::memberp varid-listp)))))

  (defthm pair-list-nz-keys-drop-varid
    (set-equiv-quant (pair-list-nz-keys (drop-varid key list))
                     (remove-equal (varid-fix key) (pair-list-nz-keys list)))
    :hints (("Goal" :do-not-induct t)))

  )

(in-theory (disable pair-list-nz-key-equiv))

(encapsulate
    ()

  ;; --------------------------------------------------------------------------

  (def::un exists-nz-key (list)
    (declare (xargs :signature ((t) booleanp)
                    :guard (pair-listp list)
                    :congruence ((pair-list-get-equiv) equal)))
    (consp (pair-list-nz-keys list)))

  (defthm no-keys-impact
    (implies
     (not (exists-nz-key list))
     (set-equiv-quant (pair-list-nz-keys list) nil)))

  ;; --------------------------------------------------------------------------

  (def::un nz-key-count (list)
    (declare (xargs :signature ((t) natp)
                    :congruence ((pair-list-get-equiv) equal)))
    (set-size (pair-list-nz-keys list)))

  (defthm nz-key-count-drop-varid
    (equal (nz-key-count (drop-varid varid list))
           (if (list::memberp (varid-fix varid) (pair-list-nz-keys list))
               (1- (nz-key-count list))
             (nz-key-count list))))


  ;; --------------------------------------------------------------------------

  (def::un next-nz-key (list)
    (declare (xargs :signature ((t) varid-p)
                    :guard (pair-listp list)))
    (if (not (exists-nz-key list)) (varid-witness)
      (car (pair-list-nz-keys list))))

  (defthm exists-nz-key-implies-next-key-memberp
    (implies
     (exists-nz-key list)
     (list::memberp (next-nz-key list) (pair-list-nz-keys list)))
    :rule-classes (:rewrite :forward-chaining))

  ;; --------------------------------------------------------------------------

  (defthm nz-key-count-drop-next-nz-key
    (implies
     (exists-nz-key list)
     (equal (nz-key-count (drop-varid (next-nz-key list) list))
            (1- (nz-key-count list)))))

  (in-theory (disable next-nz-key))
  (in-theory (disable nz-key-count))
  (in-theory (disable exists-nz-key))

  ;; --------------------------------------------------------------------------

  )

(in-theory (enable varid-p-implies))

(defthm varid-listp-remove-equal
  (implies
   (varid-listp list)
   (varid-listp (remove-equal x list))))

;; --------------------------------------------------------------------------

(def::un >=all (a list)
  (declare (xargs :measure (len list)
                  :signature ((t t) booleanp)
                  :guard (and (varid-p a) (varid-listp list))
                  :congruence ((varid-equiv nil) equal)))
  (if (not (consp list)) t
    (let ((entry (car list)))
      (and (>= (varid-fix a) (varid-fix entry))
           (>=all a (remove-equal entry list))))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm >=all-memberp
       (implies
        (list::memberp v list)
        (equal (>=all a list)
               (and (>= (varid-fix a) (varid-fix v)) (>=all a (remove-equal v list))))))

     (defun >=all-induction2 (x y)
       (declare (xargs :measure (len x)))
       (if (not (consp x)) (list x y)
         (>=all-induction2 (remove-equal (car x) x)
                           (remove-equal (car x) y))))

     (defthm memberp-cong
       (implies
        (and
         (set-equiv-quant x y)
         (list::memberp a x))
        (list::memberp a y))
       :rule-classes (:forward-chaining))

     ))

  ;; I bet this is easier with pick-a-point ..
  (defthm set-equiv-implies-iff->=all
    (implies
     (set-equiv-quant x y)
     (iff (>=all a x)
          (>=all a y)))
    :rule-classes (:congruence)
    :hints (("Goal" :induct (>=all-induction2 x y))))

  )

(defthm >=all-member
  (implies
   (and
    (>=all x list)
    (list::memberp a list))
   (>= (varid-fix x) (varid-fix a)))
  :rule-classes (:forward-chaining :linear))

(defthm >=all-member-hyps
  (implies
   (and
    (list::memberp a list)
    (>=all (double-rewrite x) list)
    (varid-p (double-rewrite x))
    (varid-listp list))
   (<= a x))
  :rule-classes (:rewrite :forward-chaining))

(defthm >=all-chaining
  (implies
   (and
    (>=all x list)
    (>= (varid-fix v) (varid-fix x)))
   (>=all v list))
  :rule-classes (:rewrite :forward-chaining))

;; pick-a-point
(encapsulate
 ()

 (encapsulate
  (((>=all-hyps) => *)
   ((>=all-key) => *)
   ((>=all-list) => *))

  (local (defun >=all-hyps () nil))
  (local (defun >=all-key () nil))
  (local (defun >=all-list () nil))

  (defthm >=all-multiplicity-constraint
    (implies
     (>=all-hyps)
     (implies
      (list::memberp arbitrary-varid (>=all-list))
      (>= (varid-fix (>=all-key)) (varid-fix arbitrary-varid))))
    :rule-classes nil)
  )

 (local
  (defun >=all-bad-guy (a list)
    (if (not (consp list)) 0
      (let ((entry (car list)))
        (if (not (>= (varid-fix a) (varid-fix entry))) entry
          (>=all-bad-guy a (remove-equal entry list)))))))

 (local
  (defthm >=all-reduction
    (equal (>=all key list)
           (implies
            (list::memberp (>=all-bad-guy key list) list)
            (>= (varid-fix key) (varid-fix (>=all-bad-guy key list)))))))

 (defthm >=all-by-multiplicity-driver
   (implies (>=all-hyps)
            (>=all (>=all-key) (>=all-list)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        >=all-multiplicity-constraint
                        (arbitrary-varid (>=all-bad-guy (>=all-key) (>=all-list)))))))))

 (ADVISER::defadvice ADVISER::>=all-by-multiplicity
   (implies (>=all-hyps)
            (>=all (>=all-key) (>=all-list)))
   :rule-classes (:pick-a-point :driver >=all-by-multiplicity-driver))

 )

(defthm >=all-superset
  (implies
   (and
    (>=all a y)
    (subset-p x y))
   (>=all a x)))

(defthm >=all-remove-equal-implication
  (implies
   (and
    (>=all a (remove-equal b list))
    (not (>=all a list)))
   (> (varid-fix b) (varid-fix a)))
  :rule-classes (:forward-chaining :linear))

#+joe
(defthm >=all-remove-equal
  (iff (>=all a (remove-equal a list))
       (>=all a list)))

(def::un >-all (a list)
  (declare (xargs :measure (len list)
                  :signature ((t t) booleanp)
                  :guard (and (varid-p a) (varid-listp list))
                  :congruence ((varid-equiv nil) equal)))
  (if (not (consp list)) t
    (let ((entry (car list)))
      (and (> (varid-fix a) (varid-fix entry))
           (>-all a (remove-equal entry list))))))

(encapsulate
 ()

 (encapsulate
  (((>-all-hyps) => *)
   ((>-all-key) => *)
   ((>-all-list) => *))

  (local (defun >-all-hyps () nil))
  (local (defun >-all-key () nil))
  (local (defun >-all-list () nil))

  (defthm >-all-multiplicity-constraint
    (implies
     (>-all-hyps)
     (implies
      (list::memberp arbitrary-varid (>-all-list))
      (> (varid-fix (>-all-key)) (varid-fix arbitrary-varid))))
    :rule-classes nil)
  )

 (local
  (defun >-all-bad-guy (a list)
    (if (not (consp list)) 0
      (let ((entry (car list)))
        (if (not (> (varid-fix a) (varid-fix entry))) entry
          (>-all-bad-guy a (remove-equal entry list)))))))

 (local
  (defthm >-all-reduction
    (equal (>-all key list)
           (implies
            (list::memberp (>-all-bad-guy key list) list)
            (> (varid-fix key) (varid-fix (>-all-bad-guy key list)))))))

 (defthm >-all-by-multiplicity-driver
   (implies (>-all-hyps)
            (>-all (>-all-key) (>-all-list)))
   :rule-classes nil
   :hints((and stable-under-simplificationp
               '(:use ((:instance
                        >-all-multiplicity-constraint
                        (arbitrary-varid (>-all-bad-guy (>-all-key) (>-all-list)))))))))

 (ADVISER::defadvice ADVISER::>-all-by-multiplicity
   (implies (>-all-hyps)
            (>-all (>-all-key) (>-all-list)))
   :rule-classes (:pick-a-point :driver >-all-by-multiplicity-driver))

 )

(defthm >-all-is-greater-than-members-hyps
  (implies
   (and
    (list::memberp a list)
    (varid-listp list)
    (varid-p (double-rewrite varid))
    (>-all (double-rewrite varid) list))
   (< a varid)))

(defthm >-all-is-greater-than-members
  (implies
   (and
    (>-all v list)
    (list::memberp x list))
   (< (varid-fix x) (varid-fix v))))

(defthm >-all-append
  (iff (>-all x (append a b))
       (and (>-all x a)
            (>-all x b)))
  :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY-ANY)
           :do-not-induct t)))

(defthm >-all-cons
  (iff (>-all x (cons a b))
       (and (> (varid-fix x) (varid-fix a))
            (>-all x b)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (append) (>-all-append))
           :use (:instance >-all-append
                           (a (list a))))))

(defthm >-all-from->=all
  (implies
   (and
    (varid-p x)
    (varid-listp list)
    (>=all x list))
   (>-all x (remove-equal x list)))
  :hints (("Subgoal 1" :in-theory (enable VARID-EQUIV-TO-EQUAL)
           :expand (VARID-LISTP LIST)
           :induct (>=all x list))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm member-remove-equal-forward
       (implies
        (and
         (list::memberp a list)
         (not (equal a b)))
        (list::memberp a (remove-equal b list)))
       :rule-classes ((:forward-chaining :trigger-terms ((remove-equal b list)))))

     (defthm >-all-implies->=all
       (implies
        (>-all x list)
        (>=all x list)))

     (def::signature remove-equal (t varid-listp) varid-listp)

     ))

  (defthmd >-all-remove-equal->=all
    (implies
     (and
      (varid-p x)
      (varid-listp list))
     (iff (>-all x (remove-equal x list))
          (>=all x list)))
    :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY-ANY)
             :do-not-induct t)
            ("Subgoal 1.1" :cases ((equal arbitrary-varid x)))))

  )

(defthm set-equiv-implies-iff->-all
  (implies
   (set-equiv-quant x y)
   (iff (>-all a x)
        (>-all a y)))
  :hints (("Goal" :in-theory (enable ADVISER::>-ALL-BY-MULTIPLICITY-ANY)
           :do-not-induct t))
  :rule-classes (:congruence))

;; --------------------------------------------------------------------------

(def::un largest-varid (list)
  (declare (xargs :signature ((t) varid-p)
                  :measure (len list)
                  :guard (varid-listp list)))
  (if (not (consp list)) (varid-witness)
    (let ((varid (car list)))
      (if (>=all varid list) (varid-fix varid)
        (largest-varid (remove-equal varid list))))))

(defthm open->=all-on-memberp
  (implies
   (list::memberp b list)
   (iff (>=all a list)
        (if (> (varid-fix b) (varid-fix a)) nil
          (>=all a (remove-equal b list))))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm car-remove-equal-case-split
       (implies
        (case-split (not (equal varid (car list))))
        (equal (car (remove-equal varid list))
               (car list))))

     (defthm member-over-remove-equal
       (implies
        (and
         (list::memberp a list)
         (not (equal a b)))
        (list::memberp a (remove-equal b list)))
       :rule-classes ((:forward-chaining :trigger-terms ((remove-equal b list)))))

     ))

  (defthm open-largest-varid-on-memberp
    (implies
     (list::memberp varid list)
     (equal (largest-varid list)
            (if (>=all varid list) (varid-fix varid)
              (largest-varid (remove-equal varid list)))))
    :hints (("Goal" :induct (largest-varid list)
             :do-not-induct t
             :expand (largest-varid (remove-equal varid list)))
            (and stable-under-simplificationp
                 '(:cases ((equal varid (car list)))))))

)

(defun largest-varid-induction2 (x y)
  (declare (xargs :measure (len x)))
  (if (not (consp x)) (list x y)
    (let ((a (varid-fix (car x))))
      (if (and (>=all a x)
               (>=all a y)) a
        (largest-varid-induction2 (remove-equal (car x) x)
                                  (remove-equal (car x) y))))))

(defthm memberp-forward-chaining-1
  (implies
   (and
    (set-equiv-quant x y)
    (list::memberp a x))
   (list::memberp a y))
  :rule-classes (:forward-chaining))

(defthm memberp-forward-chaining-2
  (implies
   (and
    (set-equiv-quant x y)
    (list::memberp a y))
   (list::memberp a x))
  :rule-classes (:forward-chaining))

(defcong set-equiv-quant equal (largest-varid x) 1
  :hints (("Goal" :induct (largest-varid-induction2 x x-equiv))))

(defthm largest-varid-is-member
  (implies
   (and
    (consp x)
    (varid-listp x))
   (list::memberp (largest-varid x) x))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((largest-varid x)))))

;; ----------------------------------------------------------------------

(def::un largest-nz-varid (x)
  (declare (xargs :signature ((t) varid-p)
                  :guard (pair-listp x)
                  :congruence ((pair-list-get-equiv) equal)))
  (largest-varid (pair-list-nz-keys x)))

(defthm largest-varid-is-largest
  (>=all (largest-varid list) list)
  :hints (("Goal" :in-theory (disable OPEN->=ALL-ON-MEMBERP
                                      OPEN-LARGEST-VARID-ON-MEMBERP)
           :do-not-induct t
           :induct (largest-varid list))))

(defthm largest-nz-varid-is-one-of-largest
  (>=all (largest-nz-varid x) (pair-list-nz-keys x)))

(defthm largest-nz-varid-is-largest
  (>-all (largest-nz-varid x) (remove-equal (largest-nz-varid x) (pair-list-nz-keys x))))

(defthm largest-nz-varid-is-member-if-exists-nz-key
  (implies
   (exists-nz-key poly)
   (list::memberp (largest-nz-varid poly)
                  (pair-list-nz-keys poly)))
  :hints (("Goal" :in-theory (e/d (exists-nz-key) (CONSP-IMPLIES-MEMBERP-CAR)))))

(in-theory (disable largest-nz-varid))

;; ----------------------------------------------------------------------

(def::un sum-rlist (x)
  (declare (xargs :signature ((t) rationalp)))
  (if (not (consp x)) 0
    (+ (rfix (car x)) (sum-rlist (cdr x)))))

(defun len-len-induction (x y)
  (if (and (consp x) (consp y))
      (len-len-induction (cdr x) (cdr y))
    (list x y)))

(defcong list-equiv equal (sum-rlist x) 1
  :hints (("Goal" :induct (len-len-induction x-equiv x))))

;; ----------------------------------------------------------------------

;; list-equiv-pick-a-point
(encapsulate
 ()

 (encapsulate
  (((list-equiv-hyps) => *)
   ((list-equiv-left) => *)
   ((list-equiv-right) => *))

  (local (defun list-equiv-hyps () nil))
  (local (defun list-equiv-left () nil))
  (local (defun list-equiv-right () nil))

  (defthm list-equiv-multiplicity-constraint
    (implies
     (list-equiv-hyps)
     (and (equal (len (list-equiv-left)) (len (list-equiv-right)))
          (equal (nth arbitrary-index (list-equiv-left))
                 (nth arbitrary-index (list-equiv-right)))))
    :rule-classes nil)

  )

 (local
  (defun list-equiv-bad-guy (x y)
    (if (and (consp x) (consp y))
        (if (not (equal (car x) (car y))) 0
          (1+ (list-equiv-bad-guy (cdr x) (cdr y))))
      1)))

 (local
  (defthm list-equiv-reduction
    (iff (list-equiv x y)
         (and (equal (len x) (len y))
              (equal (nth (list-equiv-bad-guy x y) x)
                     (nth (list-equiv-bad-guy x y) y))))
    :hints (("Goal" :in-theory (enable nth)))))

 (defthm list-equiv-by-multiplicity-driver
   (implies (list-equiv-hyps)
            (list-equiv (list-equiv-left) (list-equiv-right)))
   :rule-classes nil
   :hints (("Goal" :use (:instance list-equiv-multiplicity-constraint
                                   (arbitrary-index (list-equiv-bad-guy (list-equiv-left) (list-equiv-right)))))))

 (ADVISER::defadvice ADVISER::list-equiv-by-multiplicity
   (implies (list-equiv-hyps)
            (list-equiv (list-equiv-left) (list-equiv-right)))
   :rule-classes (:pick-a-point :driver list-equiv-by-multiplicity-driver))

 )

(defcong list-equiv equal (nth i list) 2)
(defcong list-equiv equal (len list) 1)

;; ----------------------------------------------------------------------

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (def::un eval-pair (pair env)
    (declare (xargs :signature ((t t) rationalp)
                    :congruence ((pair-equiv env-equiv) equal)))
    (let ((pair (pair-fix! pair)))
      (let ((varid (pair->varid pair))
            (coeff (pair->coeff pair)))
        (* coeff (rfix (binding->value (get-binding varid env)))))))

  (defthm eval-pair-pair
    (equal (eval-pair (pair varid coeff) env)
           (* (rfix coeff) (rfix (binding->value (get-binding varid env))))))

  (defthm eval-pair-zero
    (equal (eval-pair (pair v 0) env)
           0))

  (defthm eval-pair-plus
    (implies
     (and (rationalp a) (rationalp b))
     (equal (eval-pair (pair v (+ a b)) env)
            (+ (eval-pair (pair v a) env)
               (eval-pair (pair v b) env)))))

  (in-theory (disable eval-pair))

  )

(in-theory (disable env-equiv))

;; ----------------------------------------------------------------------

(def::un value-list (list poly env)
  (declare (xargs :signature ((t t t) rational-listp)
                  :guard (and (varid-listp list))))
  (if (not (consp list)) nil
    (let ((varid (car list)))
      (cons (eval-pair (pair varid (get-coeff varid poly)) env)
            (value-list (cdr list) poly env)))))

(defthm nth-value-list
  (equal (nth i (value-list list poly env))
         (if (< (nfix i) (len list))
             (eval-pair (pair (nth i list) (get-coeff (nth i list) poly)) env)
           nil)))

(defthm len-value-list
  (equal (len (value-list list poly env))
         (len list)))

(defcong list-equiv list-equiv (value-list list poly env) 1)
(defcong pair-list-get-equiv list-equiv (value-list list poly env) 2)
(defcong env-equiv list-equiv (value-list list poly env) 3)

;; ----------------------------------------------------------------------

(def::un rfix-list (list)
  (declare (xargs :signature ((t) rational-listp)))
  (if (not (consp list)) nil
    (cons (rfix (car list))
          (rfix-list (cdr list)))))

(defthm len-rfix-list
  (equal (len (rfix-list list))
         (len list)))

(defthm nth-rfix-list
  (equal (nth i (rfix-list list))
         (if (< (nfix i) (len list))
             (rfix (nth i list))
           nil)))

(def::un add-rlists (x y)
  (declare (xargs :signature ((t t) rational-listp)))
  (if (and (consp x) (consp y))
      (cons (+ (rfix (car x)) (rfix (car y)))
            (add-rlists (cdr x) (cdr y)))
    (if (consp x) (rfix-list x)
      (rfix-list y))))

(defun nth-x-y (i x y)
  (if (zp i) (list i x y)
    (if (and (consp x) (consp y))
        (nth-x-y (1- i) (cdr x) (cdr y))
      (list i x y))))

(defthm rfix-identity
  (implies
   (rationalp x)
   (equal (rfix x) x)))

(in-theory (disable rfix))

(defthm nth-add-rlists
  (equal (nth i (add-rlists x y))
         (if (or (< (nfix i) (len x))
                 (< (nfix i) (len y)))
             (+ (rfix (nth i x)) (rfix (nth i y)))
           nil))
  :hints (("Goal" :induct (nth-x-y i x y))))

(defthm len-add-rlists
  (equal (len (add-rlists x y))
         (max (len x) (len y))))

(defcong list-equiv list-equiv (add-rlists x y) 1)
(defcong list-equiv list-equiv (add-rlists x y) 2)

;; ----------------------------------------------------------------------------

(def::un smaller-varids (poly)
  (declare (xargs :signature ((pair-listp) pair-listp)
                  :congruence ((pair-list-get-equiv) pair-list-get-equiv)))
  (drop-varid (largest-nz-varid poly) poly))

(def::un ordered-nz-varid-list (poly)
  (declare (xargs :signature ((t) varid-listp)
                  :guard (and (pair-listp poly))
                  :measure (nz-key-count poly)
                  :congruence ((pair-list-get-equiv) list-equiv)))
  (if (not (exists-nz-key poly)) nil
    (cons (largest-nz-varid poly)
          (ordered-nz-varid-list (smaller-varids poly)))))

(defthm ordered-nz-varid-list-is-pair-list-nz-keys
  (set-equiv-quant (ordered-nz-varid-list poly)
                   (pair-list-nz-keys poly))
  :hints (("Goal" :in-theory (enable exists-nz-key))))

;; ----------------------------------------------------------------------------

#+joe
(encapsulate
    ()

  (local
   (defthm equal-boolean-reduction
     (implies
      (booleanp x)
      (iff (equal x y)
           (and (booleanp y)
                (iff x y))))))

  (defthmd open-set-equiv-quant-on-memberp
    (implies
     (list::memberp a x)
     (iff (set-equiv-quant x y)
          (and (list::memberp a y)
               (set-equiv-quant (remove-equal a x)
                                (remove-equal a y)))))
    :hints (("Goal" :do-not-induct t)
            ("Subgoal 2'" :in-theory (disable SET-EQUIV-QUANT-IMPLIES-EQUAL-MEMBERP-2)
             :use (:instance set-equiv-quant-necc
                             (a hide)
                             (x (remove-equal a x))
                             (y (remove-equal a y))))
            ("Subgoal 1'" :in-theory (disable SET-EQUIV-QUANT-IMPLIES-EQUAL-MEMBERP-2)
             :use (:instance set-equiv-quant-necc
                             (a hide)
                             (x (remove-equal a x))
                             (y (remove-equal a y))))))

  )

(defun removex (a list)
  (declare (type t a list))
  (if (not (consp list)) nil
    (if (equal a (car list)) (removex a (cdr list))
      (cons (car list) (removex a (cdr list))))))

(defthm removex-to-remove-equal
  (equal (removex a list)
         (remove-equal a list)))

(def::un eval-pair-list-aux (keys poly env)
    (declare (xargs :signature ((t t t) rationalp)
                    :guard (true-listp keys)
                    :measure (set-size keys)
                    :congruence ((nil pair-list-get-equiv env-equiv) equal)))
    (if (not (consp keys)) 0
      (let ((varid (car keys)))
        (let ((binding (get-binding varid env)))
          (+ (* (get-coeff varid poly) (rfix (binding->value binding)))
             (eval-pair-list-aux (removex varid keys) poly env))))))

(defthm open-eval-pair-list-on-memberp
  (implies
   (list::memberp varid list)
   (equal (eval-pair-list-aux list poly env)
          (let ((binding (get-binding varid env)))
            (+ (* (get-coeff varid poly) (rfix (binding->value binding)))
               (eval-pair-list-aux (removex varid list) poly env)))))
  :hints (("Goal" :induct (eval-pair-list-aux list poly env)
           :expand (EVAL-PAIR-LIST-AUX (REMOVE-EQUAL VARID LIST)  POLY ENV))))

(defun equiv-induction (x y)
  (declare (xargs :measure (set-size x)))
  (if (not (consp x)) (list x y)
    (equiv-induction (remove-equal (car x) x) (remove-equal (car x) y))))

(defcong set-equiv-quant equal (eval-pair-list-aux keys poly env) 1
  :hints (("Goal" :induct (equiv-induction keys keys-equiv))))

(defthm eval-pair-list-remove-varid
  (equal (eval-pair-list-aux (remove-equal varid list) poly env)
         (if (list::memberp varid list)
             (let ((binding (get-binding varid env)))
               (+ (eval-pair-list-aux list poly env)
                  (- (* (get-coeff varid poly) (rfix (binding->value binding))))))
           (eval-pair-list-aux list poly env)))
  :hints (("Goal" :in-theory (enable remove-non-member)
           :do-not-induct t)))

(in-theory (disable open-eval-pair-list-on-memberp))

(theory-invariant (incompatible (:rewrite eval-pair-list-remove-varid)
                                (:rewrite open-eval-pair-list-on-memberp)))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm eval-pair-list-aux-drop-varid
    (implies
     (varid-listp list)
     (equal (eval-pair-list-aux list (drop-varid varid poly) env)
            (if (list::memberp (varid-fix varid) list)
                (let ((binding (get-binding varid env)))
                  (+ (eval-pair-list-aux list poly env)
                     (- (* (get-coeff varid poly) (rfix (binding->value binding))))))
              (eval-pair-list-aux list poly env))))
    :hints (("Goal" :induct (eval-pair-list-aux list poly env)
             :expand (eval-pair-list-aux list poly env))))

  )

;; (encapsulate
;;     ()

;;   (local
;;    (encapsulate
;;        ()

;;      (defthm alpha
;;        (implies
;;         (and
;;          (set-equiv-quant y x)
;;          (consp x))
;;         (consp y))
;;        :rule-classes (:forward-chaining))

;;      (defthm beta
;;        (set-equiv-quant (set-fix x) x)
;;        :rule-classes ((:forward-chaining :trigger-terms ((set-fix x)))))

;;      ))

;;   (def::un eval-pair-list-aux (keys poly env)
;;     (declare (xargs :signature ((t t t) rationalp)
;;                     :guard (true-listp keys)
;;                     :measure (set-size keys)
;;                     :congruence ((nil pair-list-get-equiv env-equiv) equal)))
;;     (let ((keys (set-fix keys)))
;;       (if (not (consp keys)) 0
;;         (let ((varid (car keys)))
;;           (let ((binding (get-binding varid env)))
;;             (+ (* (get-coeff varid poly) (rfix (binding->value binding)))
;;                (eval-pair-list-aux (removex varid keys) poly env)))))))

;;   )

(def::un eval-pair-list (poly env)
  (declare (xargs :signature ((t t) rationalp)
                  :congruence ((pair-list-get-equiv env-equiv) equal)))
  (eval-pair-list-aux (pair-list-nz-keys poly) poly env))

(defthm eval-pair-list-drop-varid
  (equal (eval-pair-list (drop-varid varid y) env)
         (if (list::memberp (varid-fix varid) (pair-list-nz-keys y))
             (- (eval-pair-list y env)
                (* (get-coeff varid y) (rfix (binding->value (get-binding varid env)))))
           (eval-pair-list y env)))
  :hints (("Goal" :do-not-induct t)))

(defthm eval-pair-list-no-nz-keys
  (implies
   (NOT (EXISTS-NZ-KEY LIST))
   (equal (eval-pair-list list env)
          0)))

(in-theory (disable eval-pair-list))

;; #+joe
;; (def::un eval-pair-list (poly env)
;;   (declare (xargs :signature ((t t) rationalp)
;;                   :measure (nz-key-count poly)
;;                   :guard (and (pair-listp poly))
;;                   :congruence ((pair-list-get-equiv env-equiv) equal)))
;;   (if (not (exists-nz-key poly)) 0
;;     (let ((varid (largest-nz-varid poly)))
;;       (let ((binding (get-binding varid env)))
;;         (+ (* (get-coeff varid poly) (rfix (binding->value binding)))
;;            (eval-pair-list (smaller-varids poly) env))))))

;; (in-theory (disable eval-pair-list))

;; -------------------------------------------------------------------

;; JAG - where was this going?

(defun eval-pair-list-equiv (x y env)
  (declare (type (satisfies pair-listp) x y))
  (equal (eval-pair-list x env)
         (eval-pair-list y env)))

(defun-sk eval-pair-list-equiv-bad-guy (p1 p2)
  (exists (env)
          (not (equal (eval-pair-list p1 env)
                      (eval-pair-list p2 env)))))

(defun eval-pair-list-equivp (x y)
  (eval-pair-list-equiv x y (eval-pair-list-equiv-bad-guy-witness x y)))

(defthm eval-pair-list-equivp-implication
  (implies
   (eval-pair-list-equivp p1 p2)
   (eval-pair-list-equiv p1 p2 env))
  :hints (("Goal" :use eval-pair-list-equiv-bad-guy-suff)))

;; -------------------------------------------------------------------------

(def::und set-coeff (varid value list)
  (declare (xargs :signature ((t t t) pair-listp)
                  :guard (and (pair-listp list)
                              (rationalp value)
                              (varid-p varid))
                  :congruence ((varid-equiv rational-equiv pair-list-get-equiv) pair-list-get-equiv)))
  (cons (pair varid value) (pair-list-fix list)))

(defthm get-coeff-set-coeff
  (equal (get-coeff v1 (set-coeff v2 value list))
         (if (varid-equiv v1 v2) (rfix value)
           (get-coeff v1 list)))
  :hints (("Goal" :in-theory (enable set-coeff))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm pair-list-nz-keys-set-coeff
    (set-equiv-quant (pair-list-nz-keys (set-coeff varid value y))
                     (if (equal (rfix value) 0)
                         (remove-equal (varid-fix varid) (pair-list-nz-keys y))
                       (cons (varid-fix varid) (pair-list-nz-keys y))))
    :hints (("Goal" :in-theory (enable pair-list-nz-keys set-coeff))))

  (defthm eval-pair-list-aux-set-coeff
    (implies
     (varid-listp list)
     (equal (eval-pair-list-aux list (set-coeff varid value y) env)
            (if (list::memberp (varid-fix varid) list)
                (+ (eval-pair-list-aux list y env)
                   (* (rfix value) (rfix (binding->value (get-binding varid env))))
                   (- (* (get-coeff varid y) (rfix (binding->value (get-binding varid env))))))
              (eval-pair-list-aux list y env))))
    :hints (("Goal" :induct (eval-pair-list-aux list y env))))

  (local
   (defthm cons-removal
     (implies
      (list::memberp a list)
      (set-equiv-quant (cons a list) list))))

  (defthm eval-pair-list-set-coeff
    (equal (eval-pair-list (set-coeff varid value y) env)
           (+ (eval-pair-list y env)
              (* (rfix value) (rfix (binding->value (get-binding varid env))))
              (- (* (get-coeff varid y) (rfix (binding->value (get-binding varid env)))))))
    :hints (("Goal" :in-theory (enable remove-non-member eval-pair-list)
             :cases ((list::memberp (varid-fix varid) (PAIR-LIST-NZ-KEYS Y)))
             :do-not-induct t)))

  )

;; ------------------------------------------------------------

(include-book "coi/nary/nary" :dir :system)

(encapsulate
       ()

  ;; --------------------------------------------------------------

  (defequiv+ (subset-p x y)
    :equiv   set-upper-bound-equiv
    :context set-upper-bound-ctx
    :pred    set-upper-bound-pred
    :congruences ((y set-equiv-quant))
    :keywords nil
    :skip nil
    )

  (defequiv+ (list::memberp a x)
    :pred    memberp-upper-bound-pred
    :equiv   memberp-upper-bound-equiv
    :context memberp-upper-bound-ctx
    :congruences ((x set-equiv-quant))
    :chaining-ctx set-upper-bound-ctx
    :keywords nil
    :skip nil
    )

  ;; --------------------------------------------------------------

  (defcongp+ memberp-upper-bound-equiv-cons-1
    (cons x y)
    :rhs (append maxx y)
    :cong ((x (equal maxx (memberp-upper-bound-ctx x))))
    :equiv set-upper-bound-equiv
    :skip nil
    )

  (defcongp+ memberp-upper-bound-equiv-cons-2
    (cons x y)
    :cong ((y (equal maxy (set-upper-bound-ctx y))))
    :equiv set-upper-bound-equiv
    :skip nil
    )

  (defcongp+ set-upper-bound-append
    (append x y)
    :equiv set-upper-bound-equiv
    :cong ((x (equal a (set-upper-bound-ctx x)))
           (y (equal b (set-upper-bound-ctx y))))
    :skip nil
    )

  ;; --------------------------------------------------------------

  (defthm memberp-member-upper-bound-backchaining-subset
    (implies
     (and
      (bind-contextp (a (equal max (memberp-upper-bound-ctx a))) :asymmetric t)
      (double-rewrite (subset-p max x)))
     (list::memberp a x)))

  (defthm memberp-member-upper-bound-backchaining-difference
    (implies
     (and
      (bind-contextp (a (equal max (memberp-upper-bound-ctx a))) :asymmetric t)
      (double-rewrite (not (list::memberp a (set-subtract max x)))))
     (list::memberp a x)))

  (defthm memberp-set-upper-bound-backchaining
    (implies
     (and
      (bind-contextp (x (equal max (set-upper-bound-ctx x))))
      (double-rewrite (not (list::memberp a max))))
     (not (list::memberp a x))))

  (defthm subset-p-upper-bound-backchaining
    (implies
     (and
      (bind-contextp (x (equal max (set-upper-bound-ctx x))))
      (force (double-rewrite (subset-p max z))))
     (subset-p x z)))

  (defthm >-all-upper-bound-backchaining
    (implies
     (and
      (bind-contextp (list (equal max (set-upper-bound-ctx list))))
      (force (double-rewrite (>-all varid max))))
     (>-all varid list)))

  (defthm >=all-upper-bound-backchaining
    (implies
     (and
      (bind-contextp (list (equal max (set-upper-bound-ctx list))))
      (force (double-rewrite (>=all varid max))))
     (>=all varid list)))

  (local
   (encapsulate
       ()

     (defun foo (x)
       (if (< (ifix x) 100) '(a b c) nil))

     (defthm set-upper-bound-foo-driver
       (set-upper-bound-equiv (foo x) '(a b c)))

     (in-theory (disable foo))

     (defthm set-upper-bound-append-foo-1
       (subset-p (append (foo x) (foo y) (foo z))
                 '(a b c))
       :rule-classes nil)

     (defthm set-upper-bound-append-foo-2
       (subset-p (append (foo x) (foo y) (foo z))
                 '(a b c))
       :hints (("Goal" :in-theory (disable SUBSET-P-BY-MULTIPLICITY ADVISER::SUBSET-P-BY-MULTIPLICITY)))
       :rule-classes nil)

     ))

  )

;; ------------------------------------------------------------

;; (defun poly-p (x)
(fty::defprod poly
  ((const rationalp)
   (coeff pair-list)
   )
  :equiv poly-type-equiv
  )

(def::und poly-witness ()
  (declare (xargs :signature (() poly-p)))
  (poly 0 nil))

(in-theory (disable (poly-witness)))

(def::un poly-fix! (x)
  (declare (xargs :signature ((t) poly-p)))
  (with-guard-checking :none (ec-call (poly-fix x))))

(def::un get-poly-constant (poly)
  (declare (xargs :signature ((t) rationalp)
                  :congruence ((poly-type-equiv) equal)
                  :guard (poly-p poly)))
  (poly->const (poly-fix! poly)))

(def::un get-poly-coeff (varid poly)
  (declare (xargs :signature ((t t) rationalp)
                  :guard (and (varid-p varid) (poly-p poly))
                  :congruence ((varid-equiv poly-type-equiv) equal)))
  (get-coeff varid (poly->coeff poly)))

(def::un get-poly-variables (poly)
  (declare (xargs :signature ((t) varid-listp)
                  :guard (poly-p poly)
                  :congruence ((poly-type-equiv) set-equiv-quant)))
  (pair-list-nz-keys (poly->coeff poly)))

(defthm get-poly-constant-poly
  (equal (get-poly-constant (poly const coeff))
         (rfix const)))

(defthm get-poly-coeff-poly
  (equal (get-poly-coeff varid (poly const coeff))
         (get-coeff varid coeff)))

(def::un leading-variable (poly)
  (declare (xargs :signature ((t) varid-p)
                  :guard (poly-p poly)
                  :congruence ((poly-type-equiv) equal)))
  (largest-nz-varid (poly->coeff poly)))

(defthmd leading-variable-definition
  (equal (leading-variable poly)
         (largest-varid (get-poly-variables poly)))
  :hints (("Goal" :in-theory (enable largest-nz-varid))))

(defun not-constp (poly)
  (declare (type (satisfies poly-p) poly))
  (exists-nz-key (poly->coeff poly)))

(defthmd not-constp-definition
  (iff (not-constp poly)
       (consp (get-poly-variables poly)))
  :hints (("Goal" :in-theory (enable ))))

(defun isConstant (poly)
  (declare (type (satisfies poly-p) poly))
  (not (not-constp poly)))

(defthm leading-variable-is-non-zero
  (implies
   (not-constp poly)
   (not (equal (get-poly-coeff (leading-variable poly) poly) 0)))
  :rule-classes ((:forward-chaining :trigger-terms ((leading-variable poly)))))

(def::un eval-poly (poly env)
  (declare (xargs :signature ((t t) rationalp)
                  :congruence ((poly-type-equiv env-equiv) equal)
                  :congruence-hints (("Goal" :do-not-induct t))))
  (let ((poly (poly-fix! poly)))
    (+ (get-poly-constant poly)
       (eval-pair-list (poly->coeff poly) env))))

(defthm poly-eval-const-poly
  (implies
   (not (not-constp poly))
   (equal (eval-poly poly env)
          (get-poly-constant poly))))

(defthm leading-variable-is-largest
  (>-all (leading-variable poly) (remove-equal (leading-variable poly) (get-poly-variables poly))))

(defthm leading-variable-is-in-bounding-variables-when-not-constp
  (iff (list::memberp (leading-variable poly) (get-poly-variables poly))
       (not-constp poly)))

(defthm leading-variable-is-less-than-varid-if-in-poly-variables
  (implies
   (and
    (varid-p varid)
    (>-all varid (get-poly-variables poly))
    (not-constp poly))
   (< (leading-variable poly) varid))
  :hints (("Goal" :in-theory (disable not-constp leading-variable leading-variable-is-in-bounding-variables-when-not-constp)
           :use leading-variable-is-in-bounding-variables-when-not-constp)))

(defthmd >-all-subset
  (implies
   (and
    (subset-p x y)
    (>-all a y))
   (>-all a x)))

(defthm >-all-greater-than-remove-equal
  (implies
   (> (varid-fix varid) (varid-fix  x))
   (iff (>-all varid (remove-equal x list))
        (>-all varid list)))
  :hints (("Goal" :in-theory (e/d (remove-non-member) (>-all)))))

(defthm >-all-set-subtract-append
  (implies
   (and
    (>-all varid list1)
    (>-all varid list2))
   (>-all varid (set-subtract (append list1 list2)
                              list3))))

(defthm leading-variable-is-largest-subsetp
  (implies
   (force (subset-p list (get-poly-variables poly)))
   (>-all (leading-variable poly) (remove-equal (leading-variable poly) list)))
  :hints (("Goal" :in-theory (disable leading-variable get-poly-variables)
           :use (:instance >-all-subset
                           (a (leading-variable poly))
                           (x (remove-equal (leading-variable poly) list))
                           (y (remove-equal (leading-variable poly) (get-poly-variables poly))))
           :do-not-induct t)))

(defthm >-all-means->-largest
  (implies
   (and
    (varid-p varid)
    (varid-listp list)
    (consp list)
    (>-all varid list))
   (< (largest-varid list) varid))
  :rule-classes (:linear :rewrite))

(in-theory (disable not-constp leading-variable))
(in-theory (disable get-poly-constant get-poly-coeff))
(in-theory (disable eval-poly))

;; ------------------------------------------------------------

(def::un add-pair-list (x y)
  (declare (xargs :signature ((t t) pair-listp)
                  :guard (and (pair-listp x) (pair-listp y))
                  :measure (nz-key-count x)
                  :congruence ((pair-list-get-equiv pair-list-get-equiv) pair-list-get-equiv)))
  (if (not (exists-nz-key x)) (pair-list-fix y)
    (let ((varid (largest-nz-varid x)))
      (let ((sum (+ (get-coeff varid x)
                    (get-coeff varid y))))
        (let ((y (set-coeff varid sum y)))
          (add-pair-list (smaller-varids x) y))))))

(defthm get-coeff-add-pair-list
  (equal (get-coeff varid (add-pair-list x y))
         (+ (get-coeff varid x)
            (get-coeff varid y))))

(defthm eval-pair-list-add-pair-list
  (equal (eval-pair-list (add-pair-list list res) env)
         (+ (eval-pair-list list env)
            (eval-pair-list res env))))

(defun pair-list-lost-vars (x y)
  (set-subtract (append (pair-list-nz-keys x)
                        (pair-list-nz-keys y))
                (pair-list-nz-keys (add-pair-list x y))))

(defthm member-pair-list-nz-keys-add-pair-list
  (iff (list::memberp key (pair-list-nz-keys (add-pair-list x y)))
       (and (or (list::memberp key (pair-list-nz-keys x))
                (list::memberp key (pair-list-nz-keys y)))
            (not (list::memberp key (pair-list-lost-vars x y))))))

(in-theory (disable pair-list-lost-vars))

(defthm set-upper-bound-add-pair-list-nz-keys
  (set-upper-bound-equiv (pair-list-nz-keys (add-pair-list x y))
                         (append (pair-list-nz-keys x)
                                 (pair-list-nz-keys y))))

;; -------------------------------------------------------------------------

(def::un plus (p1 p2)
  (declare (xargs :signature ((t t) poly-p)
                  :guard (and (poly-p p1) (poly-p p2))
                  :congruence ((poly-type-equiv poly-type-equiv) equal)))
  (let ((p1 (poly-fix! p1))
        (p2 (poly-fix! p2)))
    (poly
     (+ (get-poly-constant p1)
        (get-poly-constant p2))
     (add-pair-list (poly->coeff p1)
                    (poly->coeff p2)))))

(defthm get-poly-coeff-plus
  (equal (get-poly-coeff var (plus p1 p2))
         (+ (get-poly-coeff var p1)
            (get-poly-coeff var p2)))
  :hints (("Goal" :in-theory (enable get-poly-coeff))))

(defthm poly-eval-plus
  (equal (eval-poly (plus p1 p2) env)
         (+ (eval-poly p1 env)
            (eval-poly p2 env)))
  :hints (("Goal" :in-theory (enable eval-poly))))

(defthm get-poly-constant-plus
  (equal (get-poly-constant (plus p1 p2))
         (+ (get-poly-constant p1)
            (get-poly-constant p2))))

(defun plus-lost-variables (p1 p2)
  (pair-list-lost-vars (poly->coeff p1) (poly->coeff p2)))

(defthm get-poly-variables-plus
  (set-equiv-quant (get-poly-variables (plus p1 p2))
                   (set-subtract (append (get-poly-variables p1)
                                         (get-poly-variables p2))
                                 (gensym::generalize (plus-lost-variables p1 p2))))
  :hints (("Goal" :in-theory (enable gensym::generalize))))

(in-theory (disable plus-lost-variables))

(in-theory (disable plus))

(defthm set-upper-bound-get-poly-variables-plus
  (set-upper-bound-equiv (get-poly-variables (plus p1 p2))
                         (append (get-poly-variables p1)
                                 (get-poly-variables p2)))
  :hints (("Goal" :in-theory (disable get-poly-variables))))

;; -------------------------------------------------------------------------

(def::un drop-variable (varid poly)
   (declare (xargs :signature ((t t) poly-p)
                   :guard (and (varid-p varid) (poly-p poly))
                   :congruence ((varid-equiv poly-type-equiv) equal)))
   (poly (get-poly-constant poly)
         (drop-varid varid (poly->coeff poly))))

(defthm get-poly-coeff-drop-variable
  (equal (get-poly-coeff var1 (drop-variable var2 poly))
         (if (varid-equiv var1 var2) 0
           (get-poly-coeff var1 poly)))
  :hints (("Goal" :in-theory (enable get-poly-coeff))))

(defthm poly-eval-drop-variable
  (equal (eval-poly (drop-variable varid poly) env)
         (+ (eval-poly poly env)
            (- (* (get-poly-coeff varid poly) (rfix (binding->value (get-binding varid env)))))))
  :hints (("Goal" :in-theory (enable get-poly-coeff GET-POLY-CONSTANT eval-poly))))

(defthm get-poly-constant-drop-variable
  (equal (get-poly-constant (drop-variable varid p))
         (get-poly-constant p))
  :hints (("Goal" :in-theory (enable GET-POLY-CONSTANT))))

(defthm get-poly-variables-drop-variable
  (set-equiv-quant (get-poly-variables (drop-variable varid poly))
                   (remove-equal (varid-fix varid) (get-poly-variables poly))))

(in-theory (disable drop-variable))

;; -------------------------------------------------------------------------

(def::un mul-pair-list (c list)
  (declare (xargs :signature ((t t) pair-listp)
                  :guard (pair-listp list)
                  :measure (nz-key-count list)
                  :congruence ((rational-equiv nil) equal)
                  :congruence ((nil pair-list-get-equiv) pair-list-get-equiv)))
  (if (not (exists-nz-key list)) nil
    (let ((varid (largest-nz-varid list)))
      (let ((coeff (get-coeff varid list)))
        (set-coeff varid (* (rfix c) coeff)
                   (mul-pair-list c (smaller-varids list)))))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm get-coeff-mul-pair-list
    (equal (get-coeff varid (mul-pair-list c poly))
           (* (rfix c) (get-coeff varid poly))))

  (defthm eval-pair-list-mul
    (equal (eval-pair-list (mul-pair-list c poly) env)
           (* (rfix c) (eval-pair-list poly env))))

  )

(defthm pair-list-nz-keys-mul-pair-list
  (set-equiv-quant (pair-list-nz-keys (mul-pair-list c poly))
                   (if (equal (rfix c) 0) nil
                     (pair-list-nz-keys poly))))

;; -------------------------------------------------------------------------

(def::un mul (c poly)
  (declare (xargs :signature ((t t) poly-p)
                  :guard (and (rationalp c) (poly-p poly))
                  :congruence ((rational-equiv poly-type-equiv) equal)))
  (let ((c     (rfix c))
        (poly  (poly-fix! poly)))
    (poly (* c (poly->const poly))
          (mul-pair-list c (poly->coeff poly)))))

(defthm get-poly-coeff-mul
  (equal (get-poly-coeff var (mul c poly))
         (* (rfix c) (get-poly-coeff var poly)))
  :hints (("Goal" :in-theory (enable get-poly-coeff))))

(defthm poly-eval-mul
  (equal (eval-poly (mul c poly) env)
         (* (rfix c) (eval-poly poly env)))
  :hints (("Goal" :in-theory (enable get-poly-constant eval-poly))))

(defthm get-poly-constant-mul
  (equal (get-poly-constant (mul c p))
         (* (rfix c) (get-poly-constant p)))
  :hints (("Goal" :in-theory (enable get-poly-constant))))

(defthm leading-variable-mul
  (implies
   (not (equal (rfix c) 0))
   (equal (leading-variable (mul c p))
          (leading-variable p)))
  :hints (("Goal" :in-theory (enable largest-nz-varid leading-variable))))

(defthm get-poly-variables-mul
  (set-equiv-quant (get-poly-variables (mul c poly))
                   (if (equal (rfix c) 0) nil
                     (get-poly-variables poly))))

(in-theory (disable mul))

;; -------------------------------------------------------------------------

(def::un sub (p1 p2)
  (declare (xargs :signature ((t t) poly-p)
                  :guard (and (poly-p p1) (poly-p p2))
                  :congruence ((poly-type-equiv poly-type-equiv) equal)))
  (let ((p2 (mul -1 p2)))
    (plus p1 p2)))

(defthm get-poly-coeff-sub
  (equal (get-poly-coeff var (sub a b))
         (- (get-poly-coeff var a) (get-poly-coeff var b))))

(defthm poly-eval-sub
  (equal (eval-poly (sub p1 p2) env)
         (- (eval-poly p1 env)
            (eval-poly p2 env))))

(defthm get-poly-constant-sub
  (equal (get-poly-constant (sub p1 p2))
         (- (get-poly-constant p1)
            (get-poly-constant p2))))

(defun sub-lost-variables (p1 p2)
  (plus-lost-variables p1 (mul -1 p2)))

(defthm get-poly-variables-sub
  (set-equiv-quant (get-poly-variables (sub p1 p2))
                   (set-subtract (append (get-poly-variables p1)
                                         (get-poly-variables p2))
                                 (gensym::generalize (sub-lost-variables p1 p2))))
  :hints (("Goal" :in-theory (e/d (gensym::generalize) (get-poly-variables)))))

(defthm set-upper-bound-get-poly-variables-sub
  (set-upper-bound-equiv (get-poly-variables (sub p1 p2))
                         (append (get-poly-variables p1)
                                 (get-poly-variables p2)))
  :hints (("Goal" :in-theory (disable get-poly-variables))
          (and (not (equal (car (car id)) 0)) '(:in-theory (disable get-poly-variables)))))

(defthm leading-variable-is-less-than-varid-if-in-sub-variables
  (implies
   (and
    (varid-p varid)
    (not-constp (sub x y))
    (force (>-all varid (get-poly-variables (sub x y)))))
   (< (leading-variable (sub x y)) varid))
  :hints (("Goal" :in-theory (disable sub not-constp get-poly-variables leading-variable))))

(in-theory (disable sub-lost-variables))
(in-theory (disable sub))

;; -------------------------------------------------------------------------

;; (defun non-zero-coefficient (varid poly)
;;   (not (equal (get-coeff varid poly) 0)))

;; What you should really have is a symbolic
;; binding.  In other words, you should support
;; beta reduction.  You could even arrange it so
;; that the evaluation process "popped" the
;; enviornment .. which would give you a
;; termination argumnet.

;;
;;(defund bool-fix (x)
;;  (declare (type t x))
;;  (if x t nil))

;; (defun one-var-poly-p (x)
;;   (declare (type t x))
;;   (and (consp x)
;;        (let ((pair (car x)))
;;          (and
;;           (pair-p pair)
;;           (equal (pair-coeff pair) 1)))))

;; (def::und varid-of-one-var-poly (x)
;;   (declare (xargs :signature ((one-var-poly-p) natp)))
;;   (let ((pair (car x)))
;;     (pair-varid pair)))

;; =========================================

;; -------------------------------------------------------------------------

(defthm varid-implies-not-poly-p-not-quote-p
  (implies
   (varid-p x)
   (and (not (poly-p x))
        (not (quotep x))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable poly-p))))

(defthm quotep-implies-not-poly-p-not-varid-p
  (implies
   (quotep x)
   (and (not (poly-p x))
        (not (varid-p x))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable poly-p))))

(defthm poly-p-implies-not-quotep-not-varid-p
  (implies
   (poly-p x)
   (and (not (quotep x))
        (not (varid-p x))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable poly-p))))

;; -------------------------------------------------------------------------

(def::un enquote (x)
  (declare (xargs :signature ((t) quotep)))
  `(quote ,(rfix x)))

(def::un exquote (x)
  (declare (xargs :signature ((t) rationalp)
                  :guard (quotep x)))
  (if (consp (cdr x)) (rfix (cadr x))
    0))

(defthm dequote-enquote
  (equal (dequote (enquote x))
         (rfix x)))

(in-theory (disable quotep dequote enquote))
;; -------------------------------------------------------------------------

;; The "bound poly" is either a poly, a varid, or a quoted constant.
(def::un bound-poly (expr)
  (declare (xargs :signature ((t) poly-p)))
  (if (poly-p expr) expr
    (if (quotep expr) (poly (exquote expr) nil)
      (poly 0 (list (pair (varid-fix expr) 1))))))

(defthm eval-poly-bound-poly
  (equal (eval-poly (bound-poly x) env)
         (if (poly-p x) (eval-poly x env)
           (if (quotep x) (exquote x)
             (rfix (binding->value (get-binding x env))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable PAIR-LIST-NZ-KEYS
                              SET-INSERT
                              EVAL-PAIR-LIST
                              eval-poly))))

(def::type+ bound-poly-p (term)
  (declare (xargs :type-name bound-poly
                  :type-witness 0))
  (or (poly-p term)
      (quotep term)
      (varid-p term)))

(fty::deffixtype bound-poly
  :pred   bound-poly-p
  :fix    bound-poly-fix
  :equiv  bound-poly-equiv
  :define nil
  )

(in-theory (disable bound-poly bound-poly-p))

;; -------------------------------------------------------------------------

(local (in-theory (disable eval-poly-bound-poly)))

;; So variables are expressed as polynomials.
(def::und eval-ineq (term env)
  (declare (xargs :signature ((t t) booleanp)
                  :congruence ((nil env-equiv) equal)))
  (case-match term
    (('and x y)
     (let ((x (eval-ineq x env))
           (y (eval-ineq y env)))
       (and x y)))
    (('or x y)
     (let ((x (eval-ineq x env))
           (y (eval-ineq y env)))
       (or x y)))
    (('not x)
     (let ((x (eval-ineq x env)))
       (not x)))
    (('= var poly)
     (let ((x (eval-poly (bound-poly var) env))
           (y (eval-poly poly env)))
       (equal x y)))
    (('!= var poly)
     (let ((x (eval-poly (bound-poly var) env))
           (y (eval-poly poly env)))
       (not (equal x y))))
    (('< x y)
     (let ((x (eval-poly (bound-poly x) env))
           (y (eval-poly y env)))
       (< x y)))
    (('<= x y)
     (let ((x (eval-poly (bound-poly x) env))
           (y (eval-poly y env)))
       (<= x y)))
    (('> x y)
     (let ((x (eval-poly (bound-poly x) env))
           (y (eval-poly y env)))
       (> x y)))
    (('>= x y)
     (let ((x (eval-poly (bound-poly x) env))
           (y (eval-poly y env)))
       (>= x y)))
    (& nil)))

(defun eval-ineq-list (list env)
  (declare (type t list))
  (if (not (consp list)) t
    (and (eval-ineq (car list) env)
         (eval-ineq-list (cdr list) env))))

;; -------------------------------------------------------------------------


(include-book "coi/util/in-conclusion" :dir :system)

(in-theory (disable mv-nth-to-val mv-nth))

(defund stop-forward (x)
  (declare (ignore x))
  t)

(in-theory (disable (:type-prescription stop-forward)))

(defund forward-wrapper (x)
  x)

(set-state-ok t)

(defun not-in-conclusion-check-fn (top fn args mfc state)
  (declare (ignore state)
           (type t args))
  (if (not (acl2::mfc-ancestors mfc))
      (let ((args (delist args)))
        (let ((clause (mfc-clause mfc)))
          (if (if (not top) (appears-in-clause fn args nil clause)
                (if (and (equal fn 'not)
                         (consp args))
                    (member-of-clause :negated (car args) clause)
                  (member-of-clause top (cons fn args) clause)))
              nil
            (list (cons 'not-in-conclusion-free-variable `(quote t))))))
    nil))

(defmacro not-in-conclusion-check (term &key (top 'nil))
  (declare (xargs :guard (consp term)))
  `(and
    (equal not-in-conclusion-check-term (list ,@(cdr term)))
    (bind-free (not-in-conclusion-check-fn ,top ',(car term) not-in-conclusion-check-term acl2::mfc acl2::state)
               (not-in-conclusion-free-variable))))

(defthm forward-wrapper-to-stop-forward
  (implies
   (in-conclusion-check (forward-wrapper (hide term)) :top t)
   (equal (forward-wrapper (hide term))
          (and (stop-forward (hide term)) term)))
  :hints (("Goal" :expand (:free (x) (hide x))
           :in-theory (enable forward-wrapper stop-forward))))

;; (defmacro defthm-> (name term)
;;   (case-match term
;;     (('implies hyp conc)
;;      `(defthm ,name
;;         (implies
;;          (and
;;           (in-conclusion-check ,hyp :top t)
;;           (not-in-conclusion-check (stop-forward (hide ,hyp)) :top t))
;;          (iff ,hyp (and (forward-wrapper (hide ,hyp)) ,conc)))
;;         :hints (("Goal" :expand (:free (x) (hide x))
;;                  :in-theory (enable forward-wrapper)))))
;;     (t nil)))

;; (defthm-> leading-variable-forward
;;   (implies
;;    (not-constp poly)
;;    (not (equal (get-poly-coeff (leading-variable poly) poly) 0))))

;; (include-book "coi/util/skip-rewrite" :dir :system)

;; (in-theory (disable leading-variable-is-non-zero))

;; (in-theory (disable (:REWRITE MV-NTH-TO-VAL) mv-nth))

(defun tri-p (x)
  (declare (type t x))
  (or (equal x 1)
      (equal x -1)
      (equal x 0)))

(in-theory (disable tri-p))

;; -------------------------------------------------------------------------

;; (< (+ ax by cz) 0)
;; (< (+ ax by)  -cz)
;; (< (+ ax by)  -cz)

(in-theory (disable get-poly-variables))

(def::und solve (varid poly)
  (declare (xargs :signature ((varid-p poly-p) poly-p)
                  :congruence ((varid-equiv poly-type-equiv) equal)))
  (let ((c (get-poly-coeff varid poly)))
    (if (zerop c) (poly 0 nil)
      (let ((c (- c)))
        (let ((poly (drop-variable varid poly)))
          (mul (/ c) poly))))))

(defthm get-poly-variables-solve
  (set-equiv-quant (get-poly-variables (solve varid poly))
                   (if (zerop (get-poly-coeff varid poly)) nil
                     (remove-equal (varid-fix varid) (get-poly-variables poly))))
  :hints (("Goal" :in-theory (enable solve))))

;;    x
;;
;; v --
;;
;;    y

(local (include-book "arithmetic-5/top" :dir :system))
(local (in-theory (enable eval-pair)))

(defthm the-<-meaning-of-solve-1
  (implies
   (not-constp poly)
   (iff (< (rfix (binding->value (get-binding (leading-variable poly) any)))
           (eval-poly (solve (leading-variable poly) poly) any))
        (if (< 0 (get-poly-coeff (leading-variable poly) poly))
            (> 0 (eval-poly poly any))
          (< 0 (eval-poly poly any)))))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm the-<-meaning-of-solve-2
  (implies
   (not-constp poly)
   (iff (< (eval-poly (solve (leading-variable poly) poly) any)
           (rfix (binding->value (get-binding (leading-variable poly) any))))
        (if (< 0 (get-poly-coeff (leading-variable poly) poly))
            (< 0 (eval-poly poly any))
          (> 0 (eval-poly poly any)))))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm the-equality-meaning-of-solve
  (implies
   (not-constp poly)
   (iff (equal (rfix (binding->value (get-binding (leading-variable poly) any)))
               (eval-poly (solve (leading-variable poly) poly) any))
        (equal (eval-poly poly any) 0)))
  :hints (("Goal" :in-theory (enable solve)
           :do-not-induct t)))

(defthm eval-poly-const-difference
  (implies
   (not (not-constp (sub p1 p2)))
   (equal (eval-poly p1 any)
          (+ (eval-poly p2 any)
             (get-poly-constant p1)
             (- (get-poly-constant p2)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable POLY-EVAL-SUB)
           :use (:instance poly-eval-sub
                           (env any)))))

(defthm not-constp-mul-type-1
  (iff (not-constp (mul c poly))
       (and (not-constp poly)
            (not (equal (rfix c) 0))))
  :hints (("Goal" :in-theory (enable exists-nz-key not-constp mul))))

(def::und poly-lcd (poly)
  (declare (ignore poly)
           (xargs :signature ((poly-p) natp)))
  0)

(in-theory (disable member-pair-list-nz-keys-add-pair-list))
(in-theory (disable get-poly-variables-plus))
(in-theory (disable get-poly-variables-sub))

(defthm largest-varid-memberp-upper-bound
  (implies
   (and (consp list) (varid-listp list))
   (memberp-upper-bound-equiv (largest-varid list)
                              list)))

;; -------------------------------------------------------------------------

#+joe
(def::un substitute (varid value poly)
  (declare (xargs :signature ((varid-p poly-p poly-p) poly-p)))
  (let ((coeff (get-poly-coeff varid poly)))
    (plus poly (mul coeff value))))
