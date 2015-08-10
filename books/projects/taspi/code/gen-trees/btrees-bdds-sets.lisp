(in-package "ACL2")
(include-book "btrees-bdds")
(include-book "sets-lists-trees")

(defthm good-depths-through-union
  (implies (and (good-depths x z)
                (good-depths y z))
           (good-depths (my-union x y) z)))

(defthm good-taxon-bdd-alist-taxa-list-to-tree-alist-help
  (implies (and (int-symlist (double-rewrite taxa-list))
                (integerp a)
                (integerp b))
           (good-taxon-bdd-alist
            (taxa-list-to-tree-alist-help taxa-list a b))))

(defthm good-taxon-bdd-alist-taxa-list-to-tree-alist
  (implies (int-symlist (double-rewrite taxa-list))
           (good-taxon-bdd-alist
            (taxa-list-to-tree-alist taxa-list)))
  :hints (("Goal" :in-theory (enable taxa-list-to-tree-alist))))

(defthm not-member-nil-strip-cdrs-gen-taxa-list-to-tree-alist=help
  (implies (and (integerp i)
                (integerp j)
                (<= 0 j))
           (not (member-gen
                 nil
                 (strip-cdrs-gen
                  (taxa-list-to-tree-alist-help taxa-list i j)))))
  :hints (("Subgoal *1/3'''" :in-theory
           (disable consp-bits-to-tree)
           :use (:instance consp-bits-to-tree
                           (x j)))))

(defthm not-member-nil-strip-cdrs-gen-taxa-list-to-tree-alist
  (implies (<= 2 (len (double-rewrite taxa-list)))
           (not (member-gen nil
                            (strip-cdrs-gen
                             (taxa-list-to-tree-alist taxa-list)))))
  :hints (("Goal" :in-theory (enable taxa-list-to-tree-alist))))


(defthm member-cars-not-nil-cdrs
  (implies (and (good-taxon-bdd-alist taxa-tree-list)
                (member-gen x (strip-cars-gen taxa-tree-list))
                (not (member-gen nil (strip-cdrs-gen taxa-tree-list))))
           (cdr (assoc-hqual x taxa-tree-list))))

(defthm good-taxon-bdd-alist-member-strip-cars-not-consp
  (implies (and (member-gen x (strip-cars-gen taxa-tree-list))
                (good-taxon-bdd-alist taxa-tree-list))
           (not (consp x)))
  :rule-classes :forward-chaining)

(defthm member-gen-taxa-list-assoc-help
  (implies (and (member-gen x (double-rewrite taxa-list))
                (integerp i)
                (integerp j))
           (member-gen x (strip-cars-gen
                          (taxa-list-to-tree-alist-help
                           taxa-list i j)))))

(defthm member-gen-taxa-list-assoc
  (implies (member-gen x (double-rewrite taxa-list))
           (member-gen x (strip-cars-gen
                          (taxa-list-to-tree-alist taxa-list))))
  :hints (("Goal" :in-theory (enable taxa-list-to-tree-alist))))

(defthm member-strip-cars-good-taxon-bdd-assoc
  (implies (and (good-taxon-bdd-alist acc)
                (member-gen x (strip-cars-gen acc)))
           (hons-assoc-equal x acc)))

(defthm assoc-stays-through-build-fast
  (implies (and (member-gen x (strip-cars-gen y))
                (good-taxon-bdd-alist y)
                (assoc-hqual x y))
           (assoc-hqual
            x (build-fast-alist-from-alist y acc))))

(defthm assoc-good-taxon-bdd-cdr
  (implies (and (good-taxon-bdd-alist x)
                (not (member-gen nil (strip-cdrs-gen x)))
                (member-gen z (strip-cars-gen x)))
           (cdr (assoc-equal z x))))

(defthm cdr-assoc-stays
  (implies (and (good-taxon-bdd-alist y)
                (not (member-gen nil (strip-cdrs-gen y)))
                (cdr (assoc-hqual x y)))
           (cdr (assoc-hqual x (build-fast-alist-from-alist
                                y acc)))))

(defthm strip-cars-of-taxa-list-help
  (subset taxa-list
          (strip-cars-gen (taxa-list-to-tree-alist-help
                           taxa-list i j))))

(defthm strip-cars-of-taxa-list
  (subset taxa-list
          (strip-cars-gen (taxa-list-to-tree-alist taxa-list)))
  :hints (("Goal" :in-theory (enable taxa-list-to-tree-alist))))
