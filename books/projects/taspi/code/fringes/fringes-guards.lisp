;; theorems for the guards of functions in fringes

(in-package "ACL2")
(include-book "fringes")
(include-book "../replete/replete-guards")
(include-book "../gen-trees/btrees-bdds-sets")
(include-book "../gen-trees/app-rev-lists")
; cert_param: (non-acl2r)


;;;;;;;;;;;;;;;;;;;;;; ofringe ;;;;;;;;;;;;;;;;;;;;;;;;;
(defthm tip-listp-omerge-oless
  (implies (and (tip-listp x)
                (tip-listp y))
           (tip-listp (omerge-oless x y))))

(defthm tip-listp-ofringe-oless
  (and (implies (and (flag flg t)
                     (treep x))
                (tip-listp (ofringe-oless x)))
       (implies (and (flag flg nil)
                     (tree-listp x))
                (tip-listp (ofringe-oless-list x))))
  :hints (("Goal" :induct (tree-p-induction x flg))))

(verify-guards ofringe-oless)
;;;;;;;;;;;;;;;;;;;;;; ofringe ;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;; fringe-frequencies1 ;;;;;;;;;;;;;;;;;;;;
(verify-guards fringe-frequencies1)
;;;;;;;;;;;;;;;;;; fringe-frequencies1 ;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;; fringe-frequencies ;;;;;;;;;;;;;;;;;;;;

(defthm halistp-fringe-frequencies1
  (implies (alistp-gen dbfringe-frequencies)
           (alistp-gen (fringe-frequencies1 l dbterms dbfringe-frequencies))))

;;;;;;;;;;;;;;;;;; fringe-frequencies ;;;;;;;;;;;;;;;;;;;;
(verify-guards fringe-frequencies)
;;;;;;;;;;;;;;;;;; fringe-frequencies ;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;   bversions   ;;;;;;;;;;;;;;;;;;;;;;

(verify-guards btree-to-fringe-help)
(verify-guards btree-to-fringe)
(verify-guards btree-to-fringe-length)
(verify-guards btree-fringe-first)
(verify-guards bfringe-frequencies1)

;;;;;;;;;;;;;;;;;; bfringe-frequencies ;;;;;;;;;;;;;;;;;;;;

(defthm halistp-bfringe-frequencies1
  (implies
   (alistp-gen dbfringe-frequencies)
   (alistp-gen
    (bfringe-frequencies1 l dbterms
                          dbfringe-frequencies ta))))

(verify-guards bfringe-frequencies)
(verify-guards btrees-to-fringes)

;; ============== start of sort/merge- bdd-fringes ==========

(defthm mc-flatten-cdr-first-rev-flatten
  (equal (mc-flatten-cdr-first x a)
         (app (taspi-rev (taspi-flatten x)) a)))

(defthm consp-btree-to-fringe-from-x
  (implies (and (consp full-taxa-list-tree)
                x)
           (consp (btree-to-fringe x full-taxa-list-tree)))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(verify-guards merge-bdd-fringes
               :hints (("Goal" :do-not-induct t)))

(defthm good-depths-through-merge
  (implies (and (good-depths x z)
                (good-depths y z))
           (good-depths (merge-bdd-fringes x y ftlt tia) z)))

(defthm good-depths-through-sort
  (implies (good-depths x y)
           (good-depths (sort-bdd-fringes x ftlt tia) y)))

(defthm not-member-through-merge
  (implies (and (not (member-gen x (double-rewrite z)))
                (not (member-gen x (double-rewrite y))))
           (not (member-gen x (merge-bdd-fringes z y ftlt tia)))))

(defthm not-member-through-sort
  (implies (not (member-gen x (double-rewrite y)))
           (not (member-gen x (sort-bdd-fringes y ftlt tia)))))

(defthm subset-list-btrees-to-fringes-through-merge
  (implies (and (subset-list (btrees-to-fringes bdd-fringes1
                                                full-taxa-list-tree)
                             x)
                (subset-list (btrees-to-fringes bdd-fringes2
                                                full-taxa-list-tree)
                             x))
           (subset-list (btrees-to-fringes
                         (merge-bdd-fringes bdd-fringes1
                                            bdd-fringes2
                                            full-taxa-list-tree
                                            taxon-index-alist)
                         full-taxa-list-tree)
                        x)))

(defthm subset-list-btrees-to-fringes-through-evens-gen
  (implies (subset-list (btrees-to-fringes x y) z)
           (subset-list (btrees-to-fringes (evens-gen x) y) z))
  :hints (("Goal" :induct (evens-gen x))))

(defthm subset-list-btrees-to-fringes-through-sort
  (implies (subset-list (btrees-to-fringes bdd-fringes
                                           full-taxa-list-tree)
                        x)
           (subset-list (btrees-to-fringes
                         (sort-bdd-fringes bdd-fringes
                                           full-taxa-list-tree
                                           taxon-index-alist)
                         full-taxa-list-tree)
                        x)))

(verify-guards sort-bdd-fringes)
;; ================ end of sort/merge- bdd-fringes ==========
(verify-guards make-good-fringes)

(defthm alistp-gen-bfringe-frequencies1
  (implies (alistp-gen acc)
           (alistp-gen (bfringe-frequencies1 x y acc list))))

(defthm alistp-gen-bfringe-frequencies
  (alistp-gen (bfringe-frequencies l taxa-list))
  :hints (("Goal" :in-theory (enable bfringe-frequencies))))

(defthm not-member-nil-through-make-good-fringes
  (not (member-gen nil (make-good-fringes x y z))))

(defthm good-depths-make-good-fringes
  (good-depths (make-good-fringes x y z) y))

(defthm subset-list-btrees-make-good-fringes
  (subset-list (btrees-to-fringes
                (make-good-fringes list y taxa-list) y)
               taxa-list))

(defthm subset-list-btrees-make-good-fringes-rev-taxa-list
  (subset-list (btrees-to-fringes
                (make-good-fringes list y taxa-list) y)
               (app taxa-list nil)))

(verify-guards term-to-bfringes
               :hints (("Goal" :do-not-induct t)))

(defthm true-listp-make-good-fringes
  (true-listp (make-good-fringes x y z)))

(defthm true-listp-through-merge
  (implies (and (true-listp x)
                (true-listp y))
           (true-listp (merge-bdd-fringes x y z w))))

(defthm true-list-through-sort
  (implies (true-listp x)
           (true-listp (sort-bdd-fringes x y z))))

(defthm true-listp-term-to-bfringes
  (true-listp (term-to-bfringes x y))
  :rule-classes :type-prescription)

(in-theory (disable term-to-bfringes))

(defthm taspip-btree-to-fringe
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (consp outstanding-taxa)
                (balanced-tree full-taxa-list-tree)
                (<= (depth outstanding-taxa)
                    (depth full-taxa-list-tree))
                (subset (btree-to-fringe outstanding-taxa
                                         full-taxa-list-tree)
                        (get-taxa-from-taxon-index taxon-index-alist)))
           (taspip nil (btree-to-fringe outstanding-taxa
                                        full-taxa-list-tree)))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(defun full-ind (x y full)
  (if (and (consp x)
           (consp y))
      (list (full-ind (car x) (car y) (car full))
            (full-ind (cdr x) (cdr y) (cdr full)))
    (list x y full)))

(defthm first-from-full-flatten-innerds
  (implies (and (consp x)
                (<= (depth x)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                )
           (subset (taspi-rev
                    (taspi-flatten
                     (btree-to-fringe-help x full-taxa-list-tree)))
                   (taspi-rev (taspi-flatten full-taxa-list-tree)))))

(defthm first-from-full-flatten
  (implies (and (consp x)
                (<= (depth x)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree))
           (subset (btree-to-fringe x full-taxa-list-tree)
                   (taspi-rev (taspi-flatten full-taxa-list-tree))))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(defthm subset-nil-t-second-part-full-taxa
  (implies (and (consp x)
                (valid-bdd x)
                (qs-subset x '(nil . t))
                (<= (depth x) (depth (cons full-taxa-list-tree1
                                           full-taxa-list-tree2)))
                (balanced-tree (cons full-taxa-list-tree1
                                     full-taxa-list-tree2)))
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  x
                                  (cons full-taxa-list-tree1
                                        full-taxa-list-tree2))))
                   (taspi-rev (taspi-flatten full-taxa-list-tree2)))))

(defthm subset-t-nil-first-part-full-taxa
  (implies (and (consp x)
                (valid-bdd x)
                (qs-subset x '(t))
                (<= (depth x) (depth (cons full-taxa-list-tree1
                                           full-taxa-list-tree2)))
                (balanced-tree (cons full-taxa-list-tree1
                                     full-taxa-list-tree2)))
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  x
                                  (cons full-taxa-list-tree1
                                        full-taxa-list-tree2))))
                   (taspi-rev (taspi-flatten full-taxa-list-tree1)))))

(defthm subset-btree-to-fringe-help-subset
  (implies (and (qs-subset x y)
                (valid-bdd x)
                (valid-bdd y)
                (consp x)
                (consp y)
                (<= (depth x)
                    (depth full-taxa-list-tree))
                (<= (depth y)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                )
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  x
                                  full-taxa-list-tree)))
                   (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  y
                                  full-taxa-list-tree)))))
  :hints (("Goal" :induct (full-ind x y full-taxa-list-tree))
          ("Subgoal *1/47.7.1.3"
           :in-theory (disable first-from-full-flatten-innerds)
           :use (:instance first-from-full-flatten-innerds
                           (x x1) (full-taxa-list-tree
                                   full-taxa-list-tree1)))
          ("Subgoal *1/46.4.1.6"
           :in-theory (disable first-from-full-flatten-innerds)
           :use (:instance first-from-full-flatten-innerds
                           (x x1) (full-taxa-list-tree
                                   full-taxa-list-tree1)))
          ("Subgoal *1/46.4.1.5"
           :in-theory (disable first-from-full-flatten-innerds)
           :use (:instance first-from-full-flatten-innerds
                           (x x1) (full-taxa-list-tree
                                   full-taxa-list-tree1)))
          ("Subgoal *1/46.4.1.2"
           :in-theory (disable first-from-full-flatten-innerds)
           :use (:instance first-from-full-flatten-innerds
                           (x x1) (full-taxa-list-tree
                                   full-taxa-list-tree1)))
          ))

(defthm subset-btree-to-fringe-subset
  (implies (and (qs-subset x y)
                (valid-bdd x)
                (valid-bdd y)
                (<= (depth x)
                    (depth full-taxa-list-tree))
                (<= (depth y)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                )
           (subset (btree-to-fringe x
                                    full-taxa-list-tree)
                   (btree-to-fringe y
                                    full-taxa-list-tree)))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(defthm valid-bdd-list-through-merge
  (implies (and (valid-bdd-list x)
                (valid-bdd-list y))
           (valid-bdd-list (merge-bdd-fringes
                            x y
                            full-taxa-list-tree
                            taxon-index-alist))))


(defthm valid-bdd-list-through-sort
  (implies (valid-bdd-list x)
           (valid-bdd-list (sort-bdd-fringes
                            x
                            full-taxa-list-tree
                            taxon-index-alist)))
  :hints (("Goal" :in-theory (enable sort-bdd-fringes))))

(defthm subset-rev-flatten-small-depth
  (implies (and (valid-bdd under)
                (consp under)
                (<= (depth under)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (subset (taspi-rev (taspi-flatten full-taxa-list-tree))
                        list))
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  under
                                  full-taxa-list-tree)))
                   list)))

(defthm subset-btree-to-fringe-small-depth
  (implies (and (valid-bdd under)
                (<= (depth under)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (subset (taspi-rev (taspi-flatten full-taxa-list-tree))
                        list))
           (subset (btree-to-fringe under full-taxa-list-tree)
                   list)))

(defthm subset-q-and-c2-taxon-index-help
  (implies (and (consp under)
                (valid-bdd under)
                (valid-bdd required-subtrees1)
                (<= (depth under)
                    (depth full-taxa-list-tree))
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (consp (q-and-c2 required-subtrees1 under))
                (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                       required-subtrees1
                                       full-taxa-list-tree)))
                        list))
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  (q-and-c2 required-subtrees1 under)
                                  full-taxa-list-tree)))
                   list))
  :hints (("Goal" :in-theory (disable subset-btree-to-fringe-help-subset)
           :use (:instance subset-btree-to-fringe-help-subset
                           (x (q-and-c2 required-subtrees1 under))
                           (y required-subtrees1)))))

(defthm subset-q-and-c2-taxon-index
  (implies (and (consp under)
                (valid-bdd under)
                (valid-bdd required-subtrees1)
                (<= (depth under)
                    (depth full-taxa-list-tree))
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (subset (btree-to-fringe
                         required-subtrees1
                         full-taxa-list-tree)
                        list))
           (subset (btree-to-fringe
                    (q-and-c2 required-subtrees1 under)
                    full-taxa-list-tree)
                   list))
  :hints (("Goal" :expand ((btree-to-fringe
                    (q-and-c2 required-subtrees1 under)
                    full-taxa-list-tree)
                           (btree-to-fringe required-subtrees1
                                            full-taxa-list-tree)))))

(defthm to-make-easier
  (implies (and
            (not (equal under1 t))
            under1
            (qs-subset under1 required-subtrees1)
            (subset
             (taspi-rev (taspi-flatten (btree-to-fringe-help required-subtrees1
                                                 full-taxa-list-tree)))
             (get-taxa-from-taxon-index taxon-index-alist))
            (<= (depth required-subtrees1)
                (depth full-taxa-list-tree))
            (<= (depth under1)
                (depth full-taxa-list-tree))
            (valid-bdd required-subtrees1)
            (valid-bdd under1)
            (balanced-tree full-taxa-list-tree))
           (subset
            (taspi-rev
             (taspi-flatten
              (btree-to-fringe-help under1 full-taxa-list-tree)))
            (get-taxa-from-taxon-index taxon-index-alist)))
  :hints
  (("goal"
    :in-theory (disable subset-btree-to-fringe-help-subset)
    :use (:instance subset-btree-to-fringe-help-subset
                    (x under1)
                    (y required-subtrees1)))))


(defthm to-make-easier-2
  (implies (and (not (equal t under1))
                under1
                (qs-subset under1 required-subtrees1)
                (subset (btree-to-fringe required-subtrees1
                                         full-taxa-list-tree)
                        (get-taxa-from-taxon-index
                         taxon-index-alist))
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (<= (depth under1)
                    (depth full-taxa-list-tree))
                (valid-bdd required-subtrees1)
                (valid-bdd under1)
                (balanced-tree full-taxa-list-tree)
                )
           (subset (btree-to-fringe under1
                                   full-taxa-list-tree)
                   (get-taxa-from-taxon-index
                    taxon-index-alist)))
  :hints (("Goal" :in-theory (disable subset-btree-to-fringe-help-subset)
           :use (:instance subset-btree-to-fringe-help-subset
                           (x under1)
                           (y required-subtrees1)))
          ("Subgoal 1" :expand (btree-to-fringe required-subtrees1
                                                full-taxa-list-tree)))
  )


(defthm subset-list-car-sorted-subset-too
  (implies (and (consp x)
                (valid-bdd-list x)
                (not (member-gen nil (double-rewrite x)))
                (subset-list (btrees-to-fringes x full-taxa-list-tree)
                             taxa-list))
           (subset (taspi-rev (taspi-flatten (btree-to-fringe-help
                                  (car x)
                                  full-taxa-list-tree)))
                   taxa-list)))

(defthm subset-list-car-sorted-subset-too-1
  (implies (and (consp x)
                (valid-bdd-list x)
                (not (member-gen nil (double-rewrite x)))
                (subset-list (btrees-to-fringes x full-taxa-list-tree)
                             taxa-list))
           (subset (btree-to-fringe (car x) full-taxa-list-tree)
                   taxa-list)))

(defthm subset-list-btrees-to-fringes-car
  (implies (and (subset-list (btrees-to-fringes x y) z)
                (consp x)
                (consp (car x)))
           (subset (taspi-rev (taspi-flatten
                         (btree-to-fringe-help (car x) y)))
                   (taspi-rev z)))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(defthm subset-list-btrees-to-fringes-car-1
  (implies (and (subset-list (btrees-to-fringes x y) z)
                (consp x)
                (consp (car x)))
           (subset (btree-to-fringe (car x) y)
                   (taspi-rev z))))

;; Functions that first remove-brlens and then call
;; appropriate function

(defun fringe-frequencies-brlens (l)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of the list based bipartitions present in the input list
;  of trees to the number of times it appeared in the input.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees

; Details: Trees in input list may have branch lengths.  Trees should
;          all be ordered according to the same underlying taxa list."
  (declare (xargs :guard t))
  (let ((removed (remove-brlens-list l)))
    (if (and (non-tip-tree-listp removed)
             (all-same-num-tips removed))
        (fringe-frequencies removed)
      'invalid-input-to-fringe-frequencies)))

(defun bfringe-brlens (x ta)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

;  ":Doc-Section TASPI
;   Returns the bdd based bipartition implied by the (sub)tree given.~/
;   ~/
;   Arguments:
;      (1) x - a tree (usually a subtree of some larger tree)
;      (2) ta - a mapping of taxa-names their bdd based representation

;  Details: Arguments can actually be more general.  Another way to think of
;           this is that it returns the taxa names in the tree x, represented
;           as a bdd.  May require that the taxa names in the tree are keys in the
;           ta argument."
  (declare (xargs :guard t))
  (bfringe (remove-brlens x) ta))

(defun bfringe-list-brlens (x ta)
  (declare (xargs :guard t))
  (bfringe-list (remove-brlens-list x) ta))

(defun bfringe-frequencies-brlens (l taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns a mapping of the bdd based bipartitions present in the input list
;  of trees to the number of times it appeared in the input.~/
;  ~/
;  Arguments:
;     (1) l - a list of trees
;     (2) taxa-list - a list of taxa

; Details: Trees in input list may have branch lengths.  Trees should
;          all be ordered according to the taxa list given."
  (declare (xargs :guard t))
  (let ((removed (remove-brlens-list l)))
    (if (and (non-tip-tree-listp removed)
             (all-same-num-tips removed))
        (bfringe-frequencies removed taxa-list)
      'invalid-input-to-bfringe-frequencies)))

(defun term-to-bfringes-brlens (term taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the bdd based list of bipartitions for the input tree.~/
;  ~/
;  Arguments:
;     (1) term - a tree
;     (2) taxa-list - a list of taxa

;  Details: Taxa names in the given tree must be a subset of those present in
;           the taxa-list given.  Tree input may have branch lengths."
  (declare (xargs :guard t))
  (let ((removed (remove-brlens term)))
    (if (and (treep removed)
             (consp removed)
             (<= 2 (len taxa-list))
             (int-symlist taxa-list))
        (term-to-bfringes removed taxa-list)
      'invalid-input-to-term-to-bfringes)))

#||
(fringe-frequencies-brlens '((((a b) (c d)) . 4) ((e . 5) f)))

(bfringe-brlens '((((a b) (c d)) . 4) ((e . 5) f))
                '(a b c d e f))

(bfringe-list-brlens '(((((a b) (c d)) . 4) ((e . 5) f))
                       )
                     '(a b c d e f))

(bfringe-frequencies-brlens '(((((a b) (c d)) . 4) ((e . 5) f))
                              )
                            '(a b c d e f))

(term-to-bfringes-brlens '(((((a b) (c d)) . 4) ((e . 5) f))
                              )
                            '(a b c d e f))

||#
