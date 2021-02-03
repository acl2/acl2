; (certify-book "merge-sort-term-order")

(in-package "ACL2")

(include-book "perm")
(include-book "term-ordered-perms")
(include-book "convert-perm-to-how-many")

(local
 (defthm term-order-total
   (implies (not (term-order x y))
            (term-order y x))))

(defthm term-orderedp-merge-sort-term-order
  (term-orderedp (merge-sort-term-order x))
  :hints (("Goal"
           :in-theory (e/d () (term-order)))))

(defthm true-listp-merge-sort-term-order
  (implies (true-listp x)
           (true-listp (merge-sort-term-order x))))

(defthm how-many-merge-term-order
  (equal (how-many e (merge-term-order x y))
         (+ (how-many e x) (how-many e y))))

(defthm how-many-evens-and-odds
  (implies (consp x)
           (equal (+ (how-many e (evens x))
                     (how-many e (evens (cdr x))))
                  (how-many e x))))

(defthm how-many-merge-sort-term-order
  (equal (how-many e (merge-sort-term-order x))
         (how-many e x)))

; (defthm perm-merge-sort-term-order
;   (perm (merge-sort-term-order x) x))

