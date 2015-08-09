(in-package "ACL2")
(include-book "../gen-helper/sets")
(include-book "../gen-helper/fast-lists")
(include-book "tree-predicates")

;; Recognizes an alist db whose domain are all nontip trees.
(defun tree-list-domain-alistp (db)
  (declare (xargs :guard (alistp-gen db)))
  (if (atom db)
      t
    (and (consp (caar db))
         (consp (cdaar db))
         (tree-listp (caar db))
         (tree-list-domain-alistp (cdr db)))))

(defthm tree-list-domain-alistp-when-not-consp
  (implies (not (consp db))
           (equal (tree-list-domain-alistp db)
                  t)))

(defthm tree-list-domain-alistp-of-consp
  (equal (tree-list-domain-alistp (cons first rest))
         (and (consp (car first))
              (consp (cdar first))
              (tree-listp (car first))
              (tree-list-domain-alistp rest))))

(dis+ind tree-list-domain-alistp)

(defthm member-gives-assoc-hqual
  (implies (and (not (equal x nil))
                (member-gen x (get-taxa-from-taxon-index order)))
           (assoc-hqual x order)))

(defthm not-consp-taspi-t-gives-assoc-equal-first
  (implies (and (taspip t x)
                (not (taspip flg x))
                (subset (mytips x)
                        (get-taxa-from-taxon-index order)))
           (assoc-hqual (first-taxon x)
                        order))
  :hints (("Goal" :cases ((consp x)))))

(defthm subset-tips-assoc-hqual-first-taxon
  (implies (and (good-taxon-index-halist order)
                (consp x)
                (taspip flg x)
                (subset (mytips x)
                        (get-taxa-from-taxon-index order)))
           (assoc-hqual (first-taxon x) order))
  :hints (("Goal" :induct (first-taxon x))))

(defthm consp-subset-member-first-taxon
  (implies (and (subset (mytips x) y)
                (consp x)
                (taspip nil x))
           (member-gen (first-taxon x) y))
  :hints (("Subgoal *1/15'''" :cases ((consp x1)))))

(defthm member-int-or-symbol
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (member-gen x (get-taxa-from-taxon-index
                               taxon-index-alist)))
           (tip-p x))
  :rule-classes :forward-chaining)

(defthm good-index-flatten-taspip
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (true-listp x)
                (subset x
                        (get-taxa-from-taxon-index taxon-index-alist)))
           (taspip nil x))
  :hints (("Goal" :induct (true-listp x))))

(defthm not-member-nil-mytips-ans
  (implies (taspip nil ans)
           (not (member-gen nil (mytips ans)))))

(defthm member-first-taxon-tips
  (implies (and (taspip nil x)
                (consp x))
           (member-gen (first-taxon x) (mytips x))))

(defthm member-taxa-assoc-hqual
  (implies (and (good-taxon-index-halist order)
                (member-gen x (get-taxa-from-taxon-index order)))
           (assoc-hqual x order)))

(defthm assoc-car-from-subset
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (consp x)
                (subset x
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (hons-assoc-equal (car x)
                             taxon-index-alist)))

(defthm proper-subtree-member-gen
  (implies (and (proper-subtreep x tree)
                (not (proper-subtreep x parent)))
           (not (member-gen tree parent)))
  :hints (("Goal" :in-theory (enable proper-subtreep
                                     subtreep))))

;; subset implies member-hqual as well as member-equal
(defthm subset-member-hqual
  (implies (and (subset x y)
                (consp x))
           (member-hqual (car x) y)))

(defthm not-member-through-evens
  (implies (not (member-gen x (double-rewrite y)))
           (not (member-gen x (evens-gen y))))
  :hints (("Goal" :induct (evens-gen y))))

(defthm hhshrink-alist-tree-list-domain-alistp1
  (implies (and (tree-list-domain-alistp db1)
                (tree-list-domain-alistp db2))
           (tree-list-domain-alistp (hhshrink-alist db1 db2))))

(defthm hshrink-alist-tree-list-domain-alistp1
  (implies (and (tree-list-domain-alistp db1)
                (tree-list-domain-alistp db2))
           (tree-list-domain-alistp (hshrink-alist db1 db2))))

(defthm member-gen-gives-smaller-del
  (implies (member-gen x (strip-cars-gen alst))
           (< (acl2-count (del-pair x alst))
              (acl2-count alst))))

(defthm alistp-gen-through-del-pair
  (implies (alistp-gen alst)
           (alistp-gen (del-pair x alst))))

(defthm not-member-through-del-pair
  (implies (not (member-gen x (strip-cars-gen alst)))
           (not (member-gen x (strip-cars-gen (del-pair y alst))))))

;(defthm halistp-gives-alistp-gen
;  (implies (halistp x)
;           (alistp-gen x)))

(defthm subset-through-del-pair
  (implies (subset (strip-cars-gen alst) y)
           (subset (strip-cars-gen (del-pair x alst)) y)))

(defthm taspip-t-gives-member-gen-first-taxon-mytips
  (implies (taspip t x)
           (member-gen (first-taxon x) (mytips x))))

(defthm not-member-nil-mytips
  (not (member-gen nil (mytips x))))

(defthm taspip-nil-through-del-pair
  (implies (taspip nil (strip-cdrs-gen alst))
           (taspip nil (strip-cdrs-gen (del-pair x alst)))))

(defthm taspip-nil-strips-cdrs-member-gives-taspip-t
  (implies (and (taspip nil (strip-cdrs-gen alst))
                (member-gen x (strip-cars-gen alst)))
           (taspip t (cdr (assoc-hqual x alst)))))

(defthm member-gen-x-del-pair-member-original
  (implies (member-gen x (strip-cdrs-gen (del-pair y alst)))
           (member-gen x (strip-cdrs-gen alst))))

(encapsulate ()
(local (in-theory (disable strip-cdrs-gen)))

(defthm subset-x-del-pair-subset-original
  (implies (subset x (strip-cdrs-gen (del-pair y alst)))
           (subset x (strip-cdrs-gen alst)))
  :hints (("Goal" :induct (subset x (strip-cdrs-gen alst)))))
)

(defthm subset-mytips-cdr-assoc-hqual
  (subset (mytips (cdr (assoc-hqual y x)))
          (mytips (strip-cdrs-gen x))))

(defthm subset-mytips-strip-cdrs-del-pair
  (subset (mytips (strip-cdrs-gen (del-pair x alst)))
          (mytips (strip-cdrs-gen alst))))


(defthm not-int-sym-member-not-int-symlist
  (implies (and (not (integerp x))
                (not (symbolp x))
                (member-gen x (double-rewrite y)))
           (not (int-symlist y))))

(defthm not-member-nil-intsymlist
  (implies (member-gen nil (double-rewrite x))
           (not (int-symlist x))))

(defthm del-intsym-element-intsymlist-same
  (implies (or (integerp x)
               (and (symbolp x)
                    (not (equal x nil))))
           (equal (int-symlist (del x y))
                  (int-symlist y))))

(defcong perm equal (int-symlist x) 1)

(defthm not-member-not-consp-assoc
  (implies (not (member-gen x (strip-cars-gen y)))
           (not (assoc-hqual x y))))

(defthm not-member-through-build-fast
  (implies (and (not (member-gen x (strip-cdrs-gen y)))
                (not (member-gen x (strip-cdrs-gen acc))))
           (not (member-gen x (strip-cdrs-gen
                               (build-fast-alist-from-alist
                                y acc))))))

(defthm member-through-build-fast
  (implies (and (alistp-gen y)
                (member-gen x (strip-cars-gen y)))
           (member-gen x (strip-cars-gen
                          (build-fast-alist-from-alist
                           y acc)))))

