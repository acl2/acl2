;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "types")

(fty::add-fix! int :fix! ifix)

(def::type-list int
  :list-name integer-list
  ;;:refine-list-equiv nil
  )

(fty::add-fix! nat :fix! nfix)

(def::type-list nat
  :list-name nat-list
  ;;:refine-list-equiv nil
  )

(def::type-refinement nat
  :refines (int))

(defthm ifix-integerp
  (implies
   (integerp x)
   (equal (ifix x) x))
  :hints (("Goal" :in-theory (enable ifix))))

(def::type joe (x)
  :and (int)
  :fix! ifix
  :non-executable t
  )

(def::type-str foo
  (
   (field1 int)
   (field2 rational)
   ))

(def::type-str-refinement-predicate bar (x)
  :refines foo
  :fields ((field1 nat))
  :bind (field2)
  :body (< field2 field1)
  )

(def::type-str-refinement-predicate hoo (x)
  :refines foo
  :fields ((field1 nat))
  )

(def::type-str-refinement-fix hoo
  :refines foo
  :fields ((field1 nat))
  )

;;
;; refines: has fewer elements.
;;

;;
;; How does type-list-refinement differ from type-refinement (?)
;;

(def::type-properties natp (x)
  )

#+joe
(def::type-refinement integer-list
  :refines-equiv-in-theory (enable true-list-fix)
  :refines (true-list))

(def::type-predicate dave-p (x)
  :type-name dave
  :guard nil
  :non-executable nil
  :doc  nil
  :body (or (equal x 3) (equal x 2))
  :and  nil
  :or   nil  
  :negative-rules      t
  :positive-rules      t
  :forward-chain       t
  :rewrite             t
  :type-prescription   nil
  :forward-chain-and   t
  :forward-chain-or    t
  :forward-chain-cases t
  :forward-chain-body  nil
  :tau-system          t
  :disable-type-p      t
  :refines            (nat)
  :refines-type-in-theory (enable natp)
  :refines-equiv-in-theory (enable natp)
  )

;;
;; These seem to be the fundamental properties the
;; refinement fixing functions must satisfy ..
;; 
;; (implies (rtype-p (efix x)) (equal (rfix (efix x)) (efix x))) .. (duh)
;; (implies (rtype-p x) (rtype-p (efix x))) .. (duh)

;; This is the hard one:
;;  - if (not (rtype-p x)) then either (not (rtype-p (efix x))) or (equal (efix x) (rfix x))
;;
;; (implies (not (rtype-p x)) (or (not (rtype-p (efix x))) (equal (efix x) (rfix x))))
;;
;; This suggests a strategy for constructing an 'or' fixer ..
;;
;; ==================================================================
;;
;; This always works perfectly:
;;
;; T1: | ---------x--- |
;; T2:         | -o----------- |
;;
(defun t1-p (x)
  (declare (type t x))
  (and (integerp x)
       (< 0 x)
       (< x 10)))

(def::un t1a-fix (x)
  (declare (xargs :signature ((t) t1-p)))
  (if (t1-p x) x 1))

(def::un t1b-fix (x)
  (declare (xargs :signature ((t) t1-p)))
  (if (t1-p x) x 6))

(def::un t1c-fix (x)
  (declare (xargs :signature ((t) t1-p)))
  (if (t1-p x) x 8))

(def::type t1a (x)
  :type-p t1-p
  :fix! t1a-fix
  :fix-signature nil
  :disable-type-p nil
  )

;; So .. we are going to prefer the 'existing' fix
;; function.  We need to communicate this fact to
;; the equivalence relation.  Or we need to prove
;; our properties for both fixig functions (?)
(def::type t1b (x)
  :type-p t1-p
  :fix! t1b-fix
  :fix-signature nil
  :disable-type-p nil
  )

(def::type t1c (x)
  :type-p t1-p
  :fix t1c-fix
  :fix-signature nil
  )

(defun t2-p (x)
  (declare (type t x))
  (and (integerp x)
       (< 5 x)
       (< x 15)))

(def::un t2a-fix (x)
  (declare (xargs :signature ((t) t2-p)))
  (if (t2-p x) x 6))

(def::un t2b-fix (x)
  (declare (xargs :signature ((t) t2-p)))
  (if (t2-p x) x 8))

(def::un t2c-fix (x)
  (declare (xargs :signature ((t) t2-p)))
  (if (t2-p x) x 14))

(def::type t2a (x)
  :type-p t2-p
  :fix! t2a-fix
  :fix-signature nil
  )

(def::type t2b (x)
  :type-p t2-p
  :fix! t2b-fix
  :fix-signature nil
  )

(def::type t2c (x)
  :type-p t2-p
  :fix! t2c-fix
  :fix-signature nil
  )

;;
;; This always fails:
;;
;; T1: | --------x---- |
;; T2:         | --o---------- |
;;
;; Intersection: Use fixT2
;;
;; T1: | --x---------- |
;; T2:         | --o---------- |
;;
;; Intersction: cannot use either
;; fixing function.
;;
;; Union: 
;;
;; T1: | --x---------- |
;; T2:         | ----------o-- |
;;
;; ==================================================================

#+joe
(defun fix-and-type (x)
  (if (and-type-p x) x
    (let ((z (efix1 x)))
      (if (and-type-p z) z
        (let ((z (efix2 x)))
          (if (and-type-p z) z
            (efix3 x)))))))

#+joe
(defun fix-or-type (x)
  (if (or-type-p x) x
    (let ((z (rfix1 x)))
      (if (and (or (not (rtype2-p z)) (equal z (rfix2 x)))
               (or (not (rtype3-p z)) (equal z (rfix3 x)))) z
        (let ((z (rfix2 x)))
          (if (and (or (not (rtype1-p z)) (equal z (rfix1 x)))
                   (or (not (rtype2-p z)) (equal z (rfix2 x)))) z
            (rfix3 x)))))))

