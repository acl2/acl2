(in-package "ACL2")
(include-book "../gen-helper/extra")
(include-book "btrees")
(include-book "../gen-helper/bdd-functions")

(defthm valid-bdd-bits-to-tree
  (implies (and (integerp i)
                (integerp depth))
           (valid-bdd (bits-to-tree i depth)))
  :hints (("Goal" :in-theory (enable bits-to-tree valid-bdd))))

(defun good-taxon-bdd-alist (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (or (integerp (caar x))
               (and (symbolp (caar x))
                    (not (equal (caar x) nil))))
           (valid-bdd (cdar x))
           (good-taxon-bdd-alist (cdr x)))
    t))

(defthm good-taxon-bdd-alist-when-not-consp
  (implies (not (consp x))
           (equal (good-taxon-bdd-alist x)
                  t)))

(defthm good-taxon-bdd-alist-of-consp
  (equal (good-taxon-bdd-alist (cons first rest))
         (and (consp first)
              (or (integerp (car first))
                  (and (symbolp (car first))
                       (not (equal (car first) nil))))
              (valid-bdd (cdr first))
              (good-taxon-bdd-alist rest))))

(dis+ind good-taxon-bdd-alist)

(defthm valid-bdd-list-strip-cdrs-good-taxon-bdd
  (implies (good-taxon-bdd-alist x)
           (valid-bdd-list (strip-cdrs-gen x))))

(defthm good-taxon-bdd-alist-gives-valid-bdd-cdr-assoc
  (implies (good-taxon-bdd-alist tree-alist)
           (valid-bdd (cdr (assoc-hqual x tree-alist)))))

(defthm good-taxon-bdd-through-build-fast
  (implies (and (good-taxon-bdd-alist x)
                (good-taxon-bdd-alist acc))
           (good-taxon-bdd-alist
            (build-fast-alist-from-alist x acc))))

(defthm good-depths-through-subtrees-implying
  (implies (good-depths x y)
           (good-depths (subtrees-implying z x) y)))

(defthm good-depths-through-subtrees-not-implying
  (implies (good-depths x y)
           (good-depths (subtrees-not-implying z x)
                        y)))

(defthm depth-q-not
  (equal (depth (q-not x))
         (depth x)))

;; I'd love to make this one faster

(defthm depth-through-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd y))
           (<= (depth (q-and-c2 x y))
               (max (depth x)
                    (depth y))))
  :hints (("Goal" :in-theory (enable depth
                                     q-and-c2))))

(defthm depth-stays-small-through-q-and-c2
  (implies (and (valid-bdd x)
                (valid-bdd y)
                (<= (depth x)
                    other)
                (<= (depth y)
                    other))
           (<= (depth (q-and-c2 x y))
               other))
  :hints (("Goal" :in-theory (disable depth-through-q-and-c2)
           :use (:instance depth-through-q-and-c2))))

(defthm consp-full-taxa-list-tree
  (implies (and (<= (depth x)
                    (depth y))
                (consp x))
           (consp y))
  :rule-classes :forward-chaining)

(defthm valid-bdd-list-through-evens
  (implies (valid-bdd-list x)
           (valid-bdd-list (evens-gen x)))
  :hints (("Goal" :induct (evens-gen x))))
