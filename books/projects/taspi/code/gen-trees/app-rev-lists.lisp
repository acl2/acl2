(in-package "ACL2")
(include-book "sets-lists-trees")

(defthm app-nil
  (implies (true-listp x)
           (equal (app x nil)
                  x)))

(defthm true-listp-rev
  (true-listp (taspi-rev x)))

(defthm app-app
  (equal (app (app x y) z)
         (app x (app y z))))

(defthm rev-app
  (implies (true-listp l2)
           (equal (taspi-rev (app l1 l2))
                  (app (taspi-rev l2) (taspi-rev l1)))))

(defthm true-listp-flatten
  (true-listp (taspi-flatten x)))

(defthm member-app
  (implies (member-gen x (double-rewrite y))
           (member-gen x (app y a))))

(defthm subset-app
  (implies (and (consp x)
                (subset x y))
           (subset (app x a) (app y a))))

(defthm subset-a-app
  (subset x (app y x)))

(defthm member-gen-rev
  (implies (member-gen x(double-rewrite y))
           (member-gen x (taspi-rev y))))

(defthm subset-app-forward
  (equal (subset (app x y) z)
         (and (subset x z)
              (subset y z))))

(defthm subset-rev
  (implies (subset x y)
           (subset (taspi-rev x) (taspi-rev y))))

(defthm subset-app-first
  (implies (consp x)
           (subset x (app x y))))

(defthm subset-subset-app
  (implies (subset x y)
           (subset x (app y z))))

(defthm subset-rev-flatten-subset-mytips
  (implies (subset (taspi-rev (taspi-flatten x)) y)
           (subset (mytips x) y)))

(defthm mytips-app
  (implies (and (subset (mytips x) y)
                (subset (mytips u) v))
           (subset (mytips (app x u))
                   (app y v))))

(defthm subset-mytips-app
  (implies (and (subset (mytips x) y)
                (subset (mytips z) y))
           (subset (mytips (app x z)) y)))

(defthm mytips-rev-flatten=mytips
  (subset (mytips (taspi-rev (taspi-flatten x)))
          (taspi-rev (taspi-flatten x))))

(defthm mytips-rev-flatten
  (subset (mytips (taspi-rev (taspi-flatten x)))
          (mytips x)))

(defthm consp-rev-flatten
  (consp (taspi-rev (taspi-flatten x))))


(defthm car-app-of-consp-gives-car-first
  (implies (consp x)
           (equal (car (app x y))
                  (car x))))

(defthm subset-x-rev
  (implies (subset x y)
           (subset x (taspi-rev y))))

(defthm subset-x-subset-rev
  (implies (subset x y)
           (subset (taspi-rev x) y)))


(defthm taxa-list-from-fast-alist
  (equal (get-taxa-from-taxon-index (build-fast-alist-from-alist
                               (element-to-number taxa-list pos)
                               'taxon-index))
         (app taxa-list nil)))

(defthm rev-taxa-from-get-taxa
  (equal (get-taxa-from-taxon-index
          (taxa-list-to-taxon-index taxa-list))
         (app taxa-list nil))
  :hints (("Goal" :in-theory (e/d (taxa-list-to-taxon-index) ()))))

(defthm taxa-list-from-fast-alist2
  (equal (get-taxa-from-index-taxon (build-fast-alist-from-alist
                               (number-to-element taxa-list pos)
                               'index-taxon))
         (app taxa-list nil))
  :hints (("Goal" :induct (new-ind2 taxa-list pos acc))))

(defthm member-get-ints-subset-flatten
  (implies (and (good-index-taxon-halist list)
                (member-gen x (get-taxa-from-taxon-index list)))
           (subset (taspi-flatten (cdr (hons-assoc-equal x list)))
                   (get-taxa-from-index-taxon list))))

(defthm del-app
  (equal (del a (app x y))
         (if (member-gen a x)
             (app (del a x) y)
           (app x (del a y)))))

(defcong perm perm (app x y) 1)
(defcong perm perm (app x y) 2)

(local
 (defthm true-list-perm-app-cons
   (implies (true-listp x)
            (perm (app x (list y))
                  (cons y x))))
)

(defthm perm-rev-fix-true
  (perm (taspi-rev tl) (fix-true-list tl)))


(defthm perm-fix-true-list-subset-rev
  (implies (perm x (fix-true-list tl))
           (perm (taspi-rev tl) x))
  :rule-classes :forward-chaining
)
