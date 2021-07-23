(in-package "ACL2")
(include-book "fringes-guards")

(defthm subset-list-through-union
  (implies (and (subset-list (btrees-to-fringes
                              x ftlt) z)
                (subset-list (btrees-to-fringes
                              y ftlt) z))
           (subset-list (btrees-to-fringes
                         (my-union x y)
                         ftlt) z)))

(defthm not-member-nil-term-to-bfringes
  (not (member-gen nil (term-to-bfringes tree taxa-list)))
  :hints (("Goal" :in-theory (enable term-to-bfringes))))

(defthm subset-list-btrees-to-fringes-of-term-to-bfringes
  (subset-list (btrees-to-fringes
                (term-to-bfringes term taxa-list)
                (build-taxa-list-tree taxa-list))
               taxa-list)
  :hints (("Goal" :in-theory (enable term-to-bfringes))))

(defthm good-depths-term-to-bfringes
  (good-depths (term-to-bfringes tree taxa-list)
               (build-taxa-list-tree taxa-list))
  :hints (("Goal" :in-theory (enable term-to-bfringes))))

(defthm subset-list-union-cdr
  (implies (subset-list (btrees-to-fringes
                         (my-union x y)
                         ftlt) z)
           (subset-list (btrees-to-fringes
                         (my-union x (cdr y))
                         ftlt) z)))
(defthm valid-bdd-bfringe
  (and (implies (and (flag flg t)
                     (good-taxon-bdd-alist tree-alist))
                (valid-bdd (bfringe x tree-alist)))
       (implies (and (flag flg nil)
                     (good-taxon-bdd-alist tree-alist))
                (valid-bdd (bfringe-list x tree-alist))))
  :hints (("Goal" :induct (tree-p-induction x flg))
          ("Subgoal *1/2'''" :expand (bfringe x tree-alist))))


(defthm member-taxa-list-bfringe-non-nil
  (and (implies (and (flag flg t)
                     (consp x)
                     (subset x
                             (strip-cars-gen taxa-tree-list))
                     (not (member-gen nil (strip-cdrs-gen
                                           taxa-tree-list)))
                     (good-taxon-bdd-alist taxa-tree-list))
                (bfringe x taxa-tree-list))
       (implies (and (flag flg nil)
                     (consp x)
                     (subset x
                             (strip-cars-gen taxa-tree-list))
                     (not (member-gen nil (strip-cdrs-gen
                                           taxa-tree-list)))
                     (good-taxon-bdd-alist taxa-tree-list))
                (bfringe-list x taxa-tree-list)))
  :hints (("Goal" :induct (tree-p-induction x flg))
          ("Subgoal *1/2.9'''" :in-theory (disable q-or-if-either)
           :use (:instance q-or-if-either
                           (x (cdr (assoc-hqual x1 taxa-tree-list)))
                           (y nil)))
          ("Subgoal *1/2.3'''" :expand (bfringe x1 taxa-tree-list))
          ("Subgoal *1/1'''" :expand (bfringe x taxa-tree-list))))


(defthm member-gen-taxa-list-bfringe
  (implies (and (member-gen x (double-rewrite taxa-list))
                (<= 2 (len (double-rewrite taxa-list)))
                (int-symlist (double-rewrite taxa-list)))
           (bfringe x (taxa-list-to-tree-alist taxa-list)))
  :hints (("Goal" :cases ((consp x)))))

(defthm bfringe-non-nil
  (implies (and (subset x taxa-list)
                (consp x)
                (int-symlist (double-rewrite taxa-list))
                (<= 2 (len (double-rewrite taxa-list))))
           (bfringe x
                    (taxa-list-to-tree-alist taxa-list)))
  :hints (("Subgoal *1/3'''" :in-theory (disable q-or-if-either)
           :use (:instance q-or-if-either
                           (x (bfringe x1 (taxa-list-to-tree-alist
                                           taxa-list)))
                           (y (bfringe-list
                               x2
                               (taxa-list-to-tree-alist taxa-list)))))))

#|
The following is the beginning of the lemmas needed to verify the guards
given for the compute-consensus and tree-compatibility functions.

SKIP!!!
(skip-proofs
(defthm SKIP-valid-bdd-list-strip-cars-gen-bfringe-frequencies
  (valid-bdd-list (strip-cars-gen
                   (bfringe-frequencies x taxa-list))))
)

(defthm valid-bdd-list-through-make-good-fringes
  (implies (valid-bdd-list x)
           (valid-bdd-list (make-good-fringes x y z))))

(defthm valid-bdd-list-term-to-bfringes
  (valid-bdd-list (term-to-bfringes tree taxa-list))
  :hints (("Goal" :in-theory (enable term-to-bfringes))))


;(defthm bfringe-through-build-fast-help
;  (and (implies (and (flag flg t)
;                     (good-taxon-bdd-alist y)
;                     (good-taxon-bdd-alist acc)
;                     (not (member-gen nil (strip-cdrs-gen y)))
;                     (not (member-gen nil (strip-cdrs-gen acc)))
;                     (bfringe x y)
;                     (subset x (strip-cars-gen y))
;                     (consp x))
;                (bfringe x
;                         (build-fast-alist-from-alist-acc y acc)))
;       (implies (and (flag flg nil)
;                     (good-taxon-bdd-alist y)
;                     (good-taxon-bdd-alist acc)
;                     (not (member-gen nil (strip-cdrs-gen y)))
;                     (not (member-gen nil (strip-cdrs-gen acc)))
;                     (bfringe-list x y)
;                     (subset x (strip-cars-gen y))
;                     (consp x))
;                (bfringe-list x
;                         (build-fast-alist-from-alist-acc y acc))))
;  :hints (("Goal" :induct (tree-p-induction x flg))
;          ("Subgoal *1/2.12'4'" :in-theory (disable q-or-if-either)
;           :use (:instance
;                 q-or-if-either
;                 (x (cdr
;                     (assoc-hqual
;                      x1
;                      (build-fast-alist-from-alist-acc y acc))))
;                 (y (bfringe-list
;                     x2
;                     (build-fast-alist-from-alist-acc
;                      y acc)))))
;          ("Subgoal *1/2.4'4'" :in-theory (disable q-or-if-either)
;           :use (:instance
;                 q-or-if-either
;                 (x (cdr
;                     (assoc-hqual
;                      x1
;                      (build-fast-alist-from-alist-acc y acc))))
;                 (y (bfringe-list
;                     x2
;                     (build-fast-alist-from-alist-acc
;                      y acc)))))
;          ("Subgoal *1/1'''" :expand
;           (bfringe x (build-fast-alist-from-alist-acc y acc)))
;))

; Use above hints to make the below work
;; SKIP!!!!
(skip-proofs
(defthm bfringe-through-build-fast
  (implies (and (bfringe x y)
                (subset x (strip-cars-gen y))
                (not (member-gen nil (strip-cdrs-gen y)))
                (not (member-gen nil (strip-cdrs-gen acc)))
                (good-taxon-bdd-alist y)
                (good-taxon-bdd-alist acc)
                )
           (bfringe x (build-fast-alist-from-alist y acc))))
;  :hints (("Goal" :in-theory (enable build-fast-alist-from-alist))
;          ("Goal'" :cases ((consp x)))))
)

;; SKIP!!!
(skip-proofs
 (defthm SKIP-good-depth-bfringe
   (implies (and (int-symlist taxa-list)
                 (subset tips-seen taxa-list))
            (<= (depth
                 (bfringe tips-seen
                          (build-fast-alist-from-alist
                           (taxa-list-to-tree-alist taxa-list)
                           acc)))
                (ilog2 (len taxa-list)))))
)

;; SKIP!!!
(skip-proofs
 (defthm SKIP-subset-btree-to-fringe-bfringe
   (implies (and (int-symlist taxa-list)
                 (subset tips-seen taxa-list))
            (subset (btree-to-fringe
                     (bfringe tips-seen
                              (build-fast-alist-from-alist
                               (taxa-list-to-tree-alist taxa-list)
                               acc))
                     (build-taxa-list-tree taxa-list))
                    taxa-list)))
)

This is the needed lemma to prove guard of compute-consensus
(skip-proofs
 (defthm SKIP-good-depths-strip-cars-bfringe-frequencies
   (implies (and (int-symlist taxa-list)
                 (<= 2 (len taxa-list)))
            (good-depths (strip-cars-gen (bfringe-frequencies
                                          list-of-trees
                                          taxa-list))
                         (build-taxa-list-tree taxa-list))))
)

|#
