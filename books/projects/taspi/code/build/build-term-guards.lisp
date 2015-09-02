(in-package "ACL2")
(include-book "build-term")
(include-book "../fringes/fringes-guards")

(verify-guards orderly-cons
               :hints (("Subgoal 4'''" :cases ((consp l1)))))

(defthm taspip-through-orderly-cons
  (implies (and (taspip t x)
                (taspip flg y))
           (taspip flg2 (orderly-cons x y taxon-index-alist))))

(defthm taspip-through-orderly-append
  (implies (and (taspip flg x)
                (taspip flg2 y))
           (taspip flg2 (orderly-append x y taxon-index-alist))))

(defthm subset-mytips-orderly-cons
  (subset (mytips (orderly-cons x y taxon-index-alist))
          (append (mytips x) (mytips y))))

(defthm subset-mytips-orderly-append
  (subset (mytips (orderly-append x y taxon-index-alist))
          (append (mytips x) (mytips y)))
  :hints (("Subgoal *1/1'''" :in-theory
           (disable subset-mytips-orderly-cons)
           :use (:instance subset-mytips-orderly-cons
                           (x x1)
                           (y (orderly-append x2 y taxon-index-alist))))))

(verify-guards orderly-append
               :hints (("Subgoal 3'"
                        :in-theory (disable
                                    subset-mytips-orderly-append)
                        :use (:instance
                              subset-mytips-orderly-append
                              (x l4) (y l2)))
                       ("Subgoal 1'''" :cases ((consp l3)))))

(defthm consp-through-orderly-append
  (implies (consp x)
           (consp (orderly-append x y taxon-index-alist))))

(defthm taspip-orderly-cons-flat
  (implies (and (taspip nil ans)
                (good-taxon-index-halist taxon-index-alist)
                (member-gen x
                            (get-taxa-from-taxon-index
                             taxon-index-alist)))
           (taspip flg (orderly-cons x ans taxon-index-alist)))
  :hints (("Subgoal *1/4''" :cases (flg))))

(defthm taspip-orderly-append-flat
  (implies (and (taspip nil ans)
                (consp ans)
                (subset x (get-taxa-from-taxon-index taxon-index-alist))
                (good-taxon-index-halist taxon-index-alist))
           (taspip flg
                   (orderly-append x ans taxon-index-alist)))
  :hints (("Subgoal *1/3'4'" :cases (flg))))

(defthm taspip-orderly-append-flat-consp
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (subset x (get-taxa-from-taxon-index taxon-index-alist))
                (consp x)
                (taspip nil ans))
           (taspip flg
                   (orderly-append x ans taxon-index-alist)))
    :hints (("Subgoal *1/3'4'" :cases (flg))))

(defthm consp-top-consp-build-term
  (implies (and (consp top)
                (consp full-taxa-list-tree))
           (consp (build-term-helper top under full-taxa-list-tree
                                     taxon-index-alist ans))))

(defthm taspip-flg-build-term-helper-gen
  (implies
   (and
    (not (member-gen t (double-rewrite under)))
    (not (member-gen nil (double-rewrite under)))
    (or (consp required-subtrees1)
        (consp ans))
    (qs-subset-list under required-subtrees1)
    (q-no-conflicts-list under)
    (subset (btree-to-fringe required-subtrees1
                             full-taxa-list-tree)
            (get-taxa-from-taxon-index taxon-index-alist))
    (<= (depth required-subtrees1)
        (depth full-taxa-list-tree))
    (good-depths under
                 full-taxa-list-tree)
    (valid-bdd required-subtrees1)
    (valid-bdd-list under)
    (balanced-tree full-taxa-list-tree)
    (taspip nil ans)
    (good-taxon-index-halist taxon-index-alist))
   (taspip flg
           (build-term-helper required-subtrees1
                              under
                              full-taxa-list-tree
                              taxon-index-alist ans)))
  :hints (("Goal" :induct (build-term-helper required-subtrees1
                              under
                              full-taxa-list-tree
                              taxon-index-alist ans)
           )
          ("Subgoal *1/2.14'''" :cases (flg))
          ("Subgoal *1/2.13'''" :cases (flg))
))


(defthm taspip-flg-build-term-helper
  (implies
   (and
    (not (member-gen t (double-rewrite under)))
    (not (member-gen nil (double-rewrite under)))
    (consp required-subtrees1)
    (qs-subset-list under required-subtrees1)
    (q-no-conflicts-list under)
    (subset (btree-to-fringe required-subtrees1
                             full-taxa-list-tree)
            (get-taxa-from-taxon-index taxon-index-alist))
    (<= (depth required-subtrees1)
        (depth full-taxa-list-tree))
    (good-depths under
                 full-taxa-list-tree)
    (valid-bdd required-subtrees1)
    (valid-bdd-list under)
    (balanced-tree full-taxa-list-tree)
    (good-taxon-index-halist taxon-index-alist))
   (taspip flg
           (build-term-helper required-subtrees1
                              under
                              full-taxa-list-tree
                              taxon-index-alist nil))))

;Eventually we might want something along these lines:
;
;(defthm len-through-sort-bdd-fringes
;  (implies (<= 2 (len bdd-fringes))
;           (<= 2 (len
;                 (sort-bdd-fringes bdd-fringes ftlt tia)))))
;
;(defthm taspip-flg-build-term-top
;  (implies (and (not (member-gen t bdd-fringes))
;                (not (member-gen nil bdd-fringes))
;                (subset (btree-to-fringe
;                         (car bdd-fringes)
;                         (build-taxa-list-tree taxa-list))
;                        (get-taxa-from-taxon-index
;                         (taxa-list-to-taxon-index taxa-list)))
;                (good-depths bdd-fringes
;                            (build-taxa-list-tree taxa-list))
;                (int-symlist taxa-list)
;                (<= 2 (len taxa-list))
;                (<= 2 (len bdd-fringes)))
;           (taspip t (build-term-top bdd-fringes taxa-list)))
;  :hints (("Goal" :in-theory (disable btree-to-fringe-of-consp-explicit))
;          ))


(defthm subset-mytips-ocons-subset
  (implies (and (valid-bdd under1)
                (valid-bdd required-subtrees1)
                (qs-subset under1 required-subtrees1)
                (consp under1)
                (consp required-subtrees1)
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (<= (depth under1)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (subset
                 (mytips (build-term-helper under1
                                            (subtrees-implying under1 under2)
                                            full-taxa-list-tree
                                            taxon-index-alist nil))
                 (btree-to-fringe under1
                                  full-taxa-list-tree)))
           (subset (mytips (orderly-cons
                            (build-term-helper under1 (subtrees-implying under1 under2)
                                               full-taxa-list-tree
                                               taxon-index-alist nil)
                            ans taxon-index-alist))
                   (append (btree-to-fringe required-subtrees1
                                            full-taxa-list-tree)
                           (mytips ans))))
  :hints (("Goal" :in-theory (disable subset-btree-to-fringe-subset
                                      subset-mytips-orderly-cons)
           :use (:instance subset-btree-to-fringe-subset
                           (x under1)
                           (y required-subtrees1)))
          ("Goal'''" :use (:instance subset-mytips-orderly-cons
                                     (x (build-term-helper under1 (subtrees-implying under1 under2)
                                               full-taxa-list-tree
                                               taxon-index-alist nil))
                                     (y ans)))))


(defthm mytips-build-term-subset-top-1
  (implies (and (valid-bdd under1)
                (valid-bdd required-subtrees1)
                (qs-subset under1 required-subtrees1)
                (consp under1)
                (consp required-subtrees1)
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (<= (depth under1)
                    (depth full-taxa-list-tree))
                (balanced-tree full-taxa-list-tree)
                (consp (q-and-c2 required-subtrees1 under1))
                (subset
                 (mytips (build-term-helper under1
                                            (subtrees-implying under1 under2)
                                            full-taxa-list-tree
                                            taxon-index-alist nil))
                 (btree-to-fringe under1
                                  full-taxa-list-tree)))
           (subset (append
                    (btree-to-fringe
                     (q-and-c2 required-subtrees1 under1)
                     full-taxa-list-tree)
                    (mytips (orderly-cons
                             (build-term-helper under1
                                                (subtrees-implying under1 under2)
                                                full-taxa-list-tree
                                                taxon-index-alist nil)
                             ans taxon-index-alist)))
                   (append (btree-to-fringe required-subtrees1
                                            full-taxa-list-tree)
                           (mytips ans))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable subset-btree-to-fringe-subset
                               subset-append-subset
                               )
           :use (:instance subset-btree-to-fringe-subset
                           (x (q-and-c2 required-subtrees1 under1))
                           (y required-subtrees1)))
          ("Goal'''" :use
           (:instance subset-append-subset
                      (x (btree-to-fringe
                          (q-and-c2 required-subtrees1 under1)
                          full-taxa-list-tree))
                      (z (mytips (orderly-cons
                                  (build-term-helper under1
                                                     (subtrees-implying under1 under2)
                                                     full-taxa-list-tree
                                                     taxon-index-alist nil)
                                  ans taxon-index-alist)))
                      (y (btree-to-fringe required-subtrees1
                                          full-taxa-list-tree))
                      (w (mytips ans))))
          ))


(defthm mytips-btree-to-fringe
  (subset (mytips (btree-to-fringe x full-taxa-list-tree))
          (btree-to-fringe x full-taxa-list-tree))
  :hints (("Goal" :in-theory (enable btree-to-fringe))))

(defthm mytips-build-term-subset-top
  (implies (and (good-taxon-index-halist taxon-index-alist)
                (valid-bdd required-subtrees1)
                (valid-bdd-list under)
                (qs-subset-list under required-subtrees1)
                (q-no-conflicts-list under)
                (consp required-subtrees1)
                (<= (depth required-subtrees1)
                    (depth full-taxa-list-tree))
                (good-depths under
                             full-taxa-list-tree)
                (subset (btree-to-fringe
                         required-subtrees1
                         full-taxa-list-tree)
                        (get-taxa-from-taxon-index taxon-index-alist))
                (balanced-tree full-taxa-list-tree)
                (not (member-gen t (double-rewrite under)))
                (not (member-gen nil (double-rewrite under))))
           (subset (mytips (build-term-helper
                            required-subtrees1
                            under
                            full-taxa-list-tree
                            taxon-index-alist ans))
                   (append (btree-to-fringe
                            required-subtrees1
                            full-taxa-list-tree)
                           (mytips ans))))
  :hints (("Goal" :induct (build-term-helper
                            required-subtrees1
                            under
                            full-taxa-list-tree
                            taxon-index-alist ans))
          ("Subgoal *1/1''" :in-theory (disable subset-mytips-orderly-append)
           :use (:instance subset-mytips-orderly-append
                           (x (btree-to-fringe
                               required-subtrees1
                               full-taxa-list-tree))
                           (y ans)))))

(defthm mytips-orderly-cons-skipper
  (implies
   (and
    (consp required-subtrees1)
    (not (member-gen t (double-rewrite required-subtrees2)))
    (not (member-gen nil (double-rewrite required-subtrees2)))
    (q-no-conflicts required-subtrees1 required-subtrees2)
    (q-no-conflicts-list required-subtrees2)
    (subset (btree-to-fringe
             required-subtrees1
             full-taxa-list-tree)
            (get-taxa-from-taxon-index taxon-index-alist))
    (subset (mytips ans)
            (get-taxa-from-taxon-index taxon-index-alist))
    (<= (depth required-subtrees1)
        (depth full-taxa-list-tree))
    (good-depths required-subtrees2 full-taxa-list-tree)
    (valid-bdd required-subtrees1)
    (valid-bdd-list required-subtrees2)
    (balanced-tree full-taxa-list-tree)
    (good-taxon-index-halist taxon-index-alist))
   (subset
    (mytips (orderly-cons
             (build-term-helper
              required-subtrees1
              (subtrees-implying required-subtrees1 required-subtrees2)
              full-taxa-list-tree
              taxon-index-alist nil)
             ans taxon-index-alist))
    (get-taxa-from-taxon-index taxon-index-alist)))
  :hints (("Goal" :in-theory (disable subset-mytips-orderly-cons
                                      mytips-build-term-subset-top
                                      first-from-full-flatten)
           :use (:instance subset-mytips-orderly-cons
                           (x (build-term-helper
                               required-subtrees1
                               (subtrees-implying required-subtrees1 required-subtrees2)
                               full-taxa-list-tree
                               taxon-index-alist nil))
                           (y ans)))
          ("Goal''" :use (:instance mytips-build-term-subset-top
                                    (under (subtrees-implying
                                            required-subtrees1
                                            required-subtrees2))
                                    (ans nil)))
          ("Goal'5'" :use (:instance first-from-full-flatten
                                     (x required-subtrees1)))))

(defthm member-gen-skipper
  (implies
   (and
    (consp required-subtrees1)
    (not (member-gen t (double-rewrite required-subtrees2)))
    (not (member-gen nil (double-rewrite required-subtrees2)))
    (q-no-conflicts required-subtrees1 required-subtrees2)
    (q-no-conflicts-list required-subtrees2)
    (subset (btree-to-fringe
             required-subtrees1
             full-taxa-list-tree)
            (get-taxa-from-taxon-index taxon-index-alist))
    (<= (depth required-subtrees1)
        (depth full-taxa-list-tree))
    (good-depths required-subtrees2 full-taxa-list-tree)
    (valid-bdd required-subtrees1)
    (valid-bdd-list required-subtrees2)
    (balanced-tree full-taxa-list-tree)
    (good-taxon-index-halist taxon-index-alist))
   (member-gen
    (first-taxon (build-term-helper
                  required-subtrees1
                  (subtrees-implying required-subtrees1
                                     required-subtrees2)
                  full-taxa-list-tree
                  taxon-index-alist nil))
    (get-taxa-from-taxon-index taxon-index-alist)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable member-first-taxon-tips
                               taspip-flg-build-term-helper
                               taspip-flg-build-term-helper-gen
                               mytips-build-term-subset-top
                               first-from-full-flatten)
           :use (:instance member-first-taxon-tips
                           (x (build-term-helper
                               required-subtrees1
                               (subtrees-implying
                                required-subtrees1
                                required-subtrees2)
                               full-taxa-list-tree
                               taxon-index-alist nil))))
          ("Subgoal 2" :use
           (:instance taspip-flg-build-term-helper
                      (under (subtrees-implying
                              required-subtrees1
                              required-subtrees2))
                      (flg nil)
                      ))
          ("Subgoal 1" :use
           (:instance mytips-build-term-subset-top
                      (under (subtrees-implying
                              required-subtrees1
                              required-subtrees2))
                      (ans nil)))
          ("Subgoal 1'''" :use
           (:instance first-from-full-flatten
                      (x required-subtrees1)))
))

(verify-guards
 build-term-helper
 :hints (("Goal"
          :do-not-induct t
          )
         ("Subgoal 15'"
          :in-theory (disable mytips-btree-to-fringe)
          :use (:instance mytips-btree-to-fringe
                          (x outstanding-taxa)))
         ("Subgoal 11'" :cases ((consp outstanding-taxa)))))


(verify-guards
 build-term-top
 :hints (("Goal" :do-not-induct t)
         ("Goal''" ; changed by J Moore after v5-0, from "Subgoal 1", for tau system
          :in-theory
          (disable not-member-through-sort valid-bdd-list-through-sort)
          :use ((:instance
                 not-member-through-sort
                 (x nil)
                 (y bdd-fringes)
                 (ftlt (build-taxa-list-tree taxa-list))
                 (tia (taxa-list-to-taxon-index taxa-list)))
                (:instance
                 valid-bdd-list-through-sort
                 (x bdd-fringes)
                 (full-taxa-list-tree
                  (build-taxa-list-tree taxa-list))
                 (taxon-index-alist
                  (taxa-list-to-taxon-index taxa-list)))))))

(defun build-term-top-guard-t (bdd-fringes taxa-list)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the tree implied by the bipartitions given.~/
;  ~/
;  Arguments:
;     (1) bdd-fringes - a list of bdd based bipartitions
;     (2) taxa-list - a list of taxa names

;  Details: BDD based bipartitions should have been created using the taxa-list
;           given.  Tree returned will be ordered according the order implied
;           by the taxa list given. Same computation as build-term-top, but
;           well-formedness of input is explicitly checked.
;           NOTE: Representation returned is rooted
;           at the *longest* bipartition but could/should probably use mv-root when
;           building an unrooted tree. "
  (declare (xargs :guard t))
  (if (and (<= 2 (len taxa-list))
           (int-symlist taxa-list)
           (valid-bdd-list bdd-fringes)
           (good-depths bdd-fringes
                        (build-taxa-list-tree taxa-list))
           (subset-list (btrees-to-fringes bdd-fringes
                                           (build-taxa-list-tree taxa-list))
                        taxa-list)
           (not (member-gen nil bdd-fringes)))
      (build-term-top bdd-fringes taxa-list)
    'bad-fringes-or-taxa-list-for-build-term))
