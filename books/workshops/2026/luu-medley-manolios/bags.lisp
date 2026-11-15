(in-package "ACL2")

(include-book "std/util/defrule" :dir :system)
(include-book "std/obags/top" :dir :system)

(defruled in-of-insert
  (iff (obag::in x (obag::insert y bag))
       (or (equal x y) (obag::in x bag)))
  :enable (obag::in-alt-def obag::occs-of-insert))

(defruled in-of-delete
  (iff (obag::in x (obag::delete y bag))
       (if (equal x y)
           (<= 2 (obag::occs x bag))
         (obag::in x bag)))
  :enable (obag::in-alt-def obag::occs-of-delete))

;;; Bridges a multiplicity condition back to membership; needed wherever a
;;; move names the same summand twice.
(defruled in-when-occs-geq-2
  (implies (<= 2 (obag::occs x bag))
           (obag::in x bag))
  :enable (obag::in-alt-def))

(encapsulate ()

  (local (in-theory (enable obag::bagp obag::bfix obag::emptyp obag::head
                            obag::tail obag::insert obag::delete)))

  (defrule bagp-of-cdr
    (implies (obag::bagp x)
             (obag::bagp (cdr x))))

  (local
   (defrule head-of-insert-is-x-or-head
     (implies (obag::bagp bag)
              (or (equal (car (obag::insert x bag)) x)
                  (equal (car (obag::insert x bag)) (car bag))))
     :rule-classes nil))

  (defrule consp-of-insert
    (consp (obag::insert x bag)))

  (local
   (defrule bagp-of-insert-cons
     (implies (and (obag::bagp bag)
                   (obag::bagp (cons a (cdr bag)))
                   (consp bag)
                   (not (<< x a))
                   (not (equal x a)))
              (obag::bagp (cons a (obag::insert x (cdr bag)))))
     :hints (("Goal" :use ((:instance head-of-insert-is-x-or-head
                                      (bag (cdr bag))))))))

  (defrule bagp-of-delete
    (implies (obag::bagp bag)
             (obag::bagp (obag::delete x bag))))

  (defrule delete-of-insert-same
    (implies (obag::bagp bag)
             (equal (obag::delete x (obag::insert x bag))
                    bag)))

  (defrule insert-of-car-into-cdr
    (implies (and (obag::bagp bag) (consp bag))
             (equal (obag::insert (car bag) (cdr bag))
                    bag)))

  (defrule insert-of-insert
    (implies (obag::bagp bag)
             (equal (obag::insert x (obag::insert y bag))
                    (obag::insert y (obag::insert x bag))))
    :rule-classes ((:rewrite :loop-stopper ((x y)))))

  ;; The converse of delete-of-insert-same.  This is what lets an operation
  ;; that deletes an element and later reinserts an equal one collapse back
  ;; to the original bag.
  (defrule insert-of-delete-when-in
    (implies (and (obag::bagp bag)
                  (obag::in x bag))
             (equal (obag::insert x (obag::delete x bag))
                    bag))
    :enable (obag::in))

  ;; The shape a delete-then-reinsert step reduces to: an element is deleted,
  ;; two others are inserted, and an equal copy of the deleted one is
  ;; reinserted outermost.  Stated directly because relying on
  ;; insert-of-insert to commute the outer insert inward depends on ACL2's
  ;; term order.
  (defrule insert-insert-delete-collapse
    (implies (and (obag::bagp bag) (obag::in x bag))
             (equal (obag::insert x
                                  (obag::insert y
                                                (obag::insert z (obag::delete x bag))))
                    (obag::insert y (obag::insert z bag))))
    :hints (("Goal"
             :use ((:instance insert-of-insert (x x) (y y)
                              (bag (obag::insert z (obag::delete x bag))))
                   (:instance insert-of-insert (x x) (y z)
                              (bag (obag::delete x bag))))
             :in-theory (disable insert-of-insert))))

  (defrule delete-of-insert-diff
    (implies (and (obag::bagp bag) (not (equal x y)))
             (equal (obag::delete x (obag::insert y bag))
                    (obag::insert y (obag::delete x bag)))))

  (defrule delete-of-delete
    (implies (obag::bagp bag)
             (equal (obag::delete x (obag::delete y bag))
                    (obag::delete y (obag::delete x bag))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))
