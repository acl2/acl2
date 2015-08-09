(in-package "PROOF")
; (include-book "omerge-good-order")
; cert_param: (non-acl2r)

(defun ofringe (flg x order)
  (declare (xargs :measure (make-ord (1+ (acl2-count x))
                                     (if flg 2 1) 0)
                  :guard (and (good-order-list order)
                              (subset
                               (mytips x)
                               (get-taxa-from-order order))
                              )
                  :verify-guards nil
                  ))

  (if flg
      (cond ((atom x) (if (null x) x (list x)))
            (t (ofringe nil x order)))
    (cond ((atom x) nil)
          (t (omerge
              (ofringe t (car x) order)
              (ofringe nil (cdr x) order) order)))))

(defthmd subset-ofringe-mytips
  (subset (ofringe flg x order) (mytips x)))

(verify-guards ofringe
               :hints (("Subgoal 4'''"
                        :use (:instance
                              subset-ofringe-mytips
                              (flg nil) (x x2)))
                       ("Subgoal 2'''"
                        :use (:instance
                              subset-ofringe-mytips
                              (flg t) (x x1)))))


(defun fringes (flg x order)
  (declare (xargs :guard (and
                          (good-order-list order)
                          (subset (mytips x)
                                  (get-taxa-from-order order)))
                  :verify-guards nil))
  (if flg
      (if (consp x)
          (cons (ofringe t x order)
                (append (fringes t (car x) order)
                        (fringes nil (cdr x) order)))
        nil)
    (if (consp x)
        (append (fringes t (car x) order)
                (fringes nil (cdr x) order))
      nil)))

(defthm true-listp-fringes
  (true-listp (fringes flg x order)))

(verify-guards fringes)

(defun first-taxon (term)
  (declare (xargs :guard t))
  (if (atom term)
      term
    (first-taxon (car term))))

(defun taspip (flg x)
  (declare (xargs :measure (make-ord (1+ (acl2-count x))
                                     1
                                     (if flg 1 0))
                  :guard t))
  (if flg
      (if (atom x)
          (or (and (symbolp x)
                   (not (equal x nil)))
              (integerp x))
        (taspip nil x))
    (if (atom x)
        (null x)
      (and (taspip t (car x))
           (taspip nil (cdr x))))))


(defthm assoc-equal-rationalp-cdr
  (implies (and (good-order-list order)
                (assoc-equal x order))
           (rationalp (cdr (assoc-equal x order)))))

(defthm not-consp-assoc-not-assoc-equal
  (implies (and (good-order-list order)
                (not (consp (assoc-equal x order))))
           (not (assoc-equal x order))))

(defthm subset-tips-assoc-equal-first-taxon
  (implies (and (good-order-list order)
                (consp x)
                (taspip flg x)
                (subset (mytips x)
                        (get-taxa-from-order order)))
           (assoc-equal (first-taxon x) order))
  :hints (("Goal" :induct (first-taxon x))))

(defun orderly-cons (x l order-alist)
  (declare (xargs :guard (and (good-order-list order-alist)
                              (taspip nil l)
                              (subset (mytips l)
                                      (get-taxa-from-order
                                       order-alist)))))
  (if (assoc-equal (first-taxon x) order-alist)
      (if (atom l)
          (cons x nil)
        (if (< (cdr (assoc-equal (first-taxon x) order-alist))
               (cdr (assoc-equal (first-taxon (car l)) order-alist)))
            (cons x l)
          (cons (car l) (orderly-cons x (cdr l) order-alist))))
      l))


(defun partstotaspi (top under order)
  (declare (xargs :guard (and (good-order-list order)
                              (true-list-listp under)
                              (subset
                               top
                               (get-taxa-from-order order))
                              (subset-list
                               under
                               top)
                              (no-conflicts-list under)
                              )
                  :verify-guards nil))
  (if (consp under)
      (orderly-cons (partstotaspi
                     (car under)
                     (get-subsets (car under)
                                  (cdr under))
                     order)
                    (partstotaspi
                     (difference top (car under))
                     (get-non-subsets (car under)
                                      (cdr under))
                     order)
                    order)
    top))


(defthm taspip-orderly-cons-int-sym
  (implies (and (good-order-list order)
                (taspip flg y)
                (or (integerp x)
                    (and (symbolp x)
                         x)))
           (taspip flg (orderly-cons x y order))))

(defthm taspip-through-orderly-cons
  (implies (and (good-order-list order)
                (taspip flg x)
                (taspip flg y)
                (subset (mytips y)
                        (get-taxa-from-order order)))
           (taspip flg (orderly-cons x y order))))


(defthm not-member-nil-get-taxa
  (implies (good-order-list order)
           (not (member-equal nil (get-taxa-from-order order)))))

(defthm member-taxa-int-sym
  (implies (and (good-order-list order)
                (member-equal x (get-taxa-from-order order)))
           (or (integerp x)
               (symbolp x)))
  :rule-classes :forward-chaining)

(defthm taspip-nil-top
  (implies (and (good-order-list order)
                (subset top (get-taxa-from-order order))
                (equal y (get-taxa-from-order order)))
           (taspip nil top))
  :hints (("Goal" :induct (subset top y))))

(defthm taspip-partstotaspi
  (implies (and (good-order-list order)
                (subset-list under
                             top)
                (subset top (get-taxa-from-order order))
                (no-conflicts-list under))
           (taspip nil (partstotaspi top under order)))
  :hints (("Goal" :induct (partstotaspi top under order))))

(defthm subset-mytips-top-top
  (implies (and (subset top (get-taxa-from-order order))
              (good-order-list order))
         (subset (mytips top) top))
  :hints (("Goal" :induct (mytips top))))

(defthm subset-mytips-orderly-cons
  (implies (and (subset (mytips x) top)
                (subset (mytips y) top))
           (subset (mytips (orderly-cons x y order)) top)))

(defthm subset-mytips-partstotaspi-top
  (implies (and (subset top
                        (get-taxa-from-order order))
                (good-order-list order)
                (no-conflicts-list under)
                (subset-list under top))
           (subset (mytips (partstotaspi top under order))
                   top))
  :hints (("Goal" :induct (partstotaspi top under order))))

(verify-guards partstotaspi
               :hints (("Subgoal 3'4'"
                        :in-theory (disable subset-mytips-partstotaspi-top)
                        :use
                        (:instance subset-mytips-partstotaspi-top
                                   (under (get-non-subsets under1 under2))
                                   (top (difference top under1))))))

(defun ordered-taspi (x order)
  (declare (xargs :guard (and (good-order-list order)
                              (taspip x x)
                              (subset (mytips x)
                                      (get-taxa-from-order order)))))
  (if (consp x)
      (if (consp (cdr x))
          (and (< (cdr (assoc-equal (first-taxon x)
                                    order))
                  (cdr (assoc-equal (first-taxon (cdr x))
                                    order)))
               (ordered-taspi (car x) order)
               (ordered-taspi (cdr x) order))
        (ordered-taspi (car x) order)) ; ending on an atom
    t))



(defun good-fringes-list (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (true-listp (car x))
           (good-fringes-list (cdr x)))
    (equal x nil)))


;; ofringe, fringe and partstotaspi


(defthm true-listp-ofringe
  (true-listp (ofringe flg x order)))

;; subset ofringe of tips, and susbet-list fringes ofringe

(defthm subset-list-fringes-ofringe
  (implies (and (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset (mytips x)
                        (get-taxa-from-order order)))
           (subset-list (fringes flg x order)
                        (ofringe flg2 x order)))
  :hints (("Subgoal *1/8.5'''"
           :use ((:instance subset-ofringe-mytips
                            (flg nil)
                            (x x1))
                 (:instance subset-ofringe-mytips
                            (flg nil)
                            (x x2))))
          ("Subgoal *1/8.4'''"
           :use ((:instance subset-ofringe-mytips
                            (flg nil)
                            (x x1))
                 (:instance subset-ofringe-mytips
                            (flg nil)
                            (x x2))))
          ("Subgoal *1/8.2'''"
           :use (:instance subset-ofringe-mytips
                           (flg nil)
                           (x x2)))
          ("Subgoal *1/8.1'''"
           :use (:instance subset-ofringe-mytips
                           (flg nil)
                           (x x2)))))


(defthm consp-car-fringes-t-ofringe-nil
  (implies (consp x)
           (equal (car (fringes t x order))
                  (ofringe nil x order))))

(deflabel top-level-singles)
(encapsulate ()

(local
(defthm get-subsets-simplification
  (implies (and (consp x)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset (mytips x)
                        (get-taxa-from-order order)))
           (equal (get-subsets (ofringe nil x order)
                               (cdr (fringes t x order)))
                  (cdr (fringes t x order))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable subset-list-fringes-ofringe
                               subset-list-get-subsets-equal)
           :use ((:instance subset-list-fringes-ofringe
                            (flg t)
                            (flg2 t))
                 (:instance subset-list-get-subsets-equal
                            (list (cdr (fringes t x order)))
                            (x (ofringe nil x order)))))))
)

(local
(defthm get-non-subsets-simplification
  (implies (and (consp x)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset (mytips x)
                        (get-taxa-from-order order)))
           (not (get-non-subsets (ofringe nil x order)
                                 (cdr (fringes t x order)))))
   :hints (("Goal" :do-not-induct t
           :in-theory (disable subset-list-fringes-ofringe
                               subset-list-get-subsets-equal)
           :use ((:instance subset-list-fringes-ofringe
                            (flg t)
                            (flg2 t))))))
)

(defthm top-level-single-gen
  (implies (and (equal (partstotaspi (ofringe nil x1 order)
                                   (cdr (fringes t x1 order))
                                   order)
                     x1)
              (ordered-taspi x1 order)
              (good-order-list order)
              (no-duplicatesp-equal (strip-cdrs order))
              (no-duplicatesp-equal (mytips x1))
              (subset (mytips x1)
                      (get-taxa-from-order order))
              (consp x1)
              (taspip nil x1)
              (consp (fringes t x1 order)))
         (equal (partstotaspi (ofringe nil x1 order)
                              (cons (ofringe nil x1 order)
                                    (cdr (fringes t x1 order)))
                              order)
                (list x1)))
  :hints (("Goal" :do-not-induct t)))

;end of encapsulate
)


(defthmd disjoint-lists-fringes
  (implies (and (not (intersect (mytips x1) (mytips x2)))
                (subset-list (fringes t x1 order)
                             (ofringe flg2 x1 order))
                (subset-list (fringes nil x2 order)
                             (ofringe flg2 x2 order))
                (subset (ofringe flg2 x1 order) (mytips x1))
                (subset (ofringe flg2 x2 order) (mytips x2)))
           (disjoint-lists (fringes t x1 order)
                           (fringes nil x2 order)))
  :hints (("Goal" :in-theory (disable subset-disjoint-disjoint)
           :use (:instance subset-disjoint-disjoint
                           (x (fringes t x1 order))
                           (y (mytips x1))
                           (u (fringes nil x2 order))
                           (v (mytips x2))))))


(defthm no-conflicts-list-get-fringes
  (implies (and (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (no-duplicatesp-equal (mytips x))
                (subset (mytips x) (get-taxa-from-order order)))
           (no-conflicts-list (fringes flg x order)))
  :hints (("Subgoal *1/19''" :use
           ((:instance subset-ofringe-mytips
                      (x x1) (flg flg2))
            (:instance subset-ofringe-mytips
                      (x x2) (flg flg2))))
          ("Subgoal *1/19'4'" :use
           (:instance disjoint-lists-fringes))
          ("Subgoal *1/9.4'''" :use
           ((:instance subset-ofringe-mytips
                      (x x1) (flg flg2))
            (:instance subset-ofringe-mytips
                      (x x2) (flg flg2))))
          ("Subgoal *1/9.4'4'" :use
           (:instance disjoint-lists-fringes))
          ("Subgoal *1/9.3'''"  :in-theory
           (disable subset-list-gives-omerge-1
                    subset-list-gives-omerge-2)
           :use
           ((:instance subset-list-gives-omerge-1
                       (x (fringes t x1 order))
                       (y (ofringe nil x1 order))
                       (z (ofringe nil x2 order)))
            (:instance subset-list-gives-omerge-2
                       (x (fringes nil x2 order))
                       (y (ofringe nil x2 order))
                       (z (ofringe nil x1 order)))
            (:instance subset-ofringe-mytips
                      (x x1) (flg nil))
            (:instance subset-ofringe-mytips
                      (x x2) (flg nil))))
          ("Subgoal *1/9.1'''" :in-theory
           (disable subset-list-gives-omerge-1
                    subset-list-gives-omerge-2)
           :use ((:instance subset-list-gives-omerge-2
                       (x (fringes nil x2 order))
                       (y (ofringe nil x2 order))
                       (z (list x1)))
                 (:instance subset-ofringe-mytips
                      (x x2) (flg nil))))
          ))


(defthm consp-top-member-equal-first-taxon-self
  (implies (and (consp x)
                (subset x (get-taxa-from-order order))
                (good-order-list order))
           (member-equal (first-taxon x) x))
  :hints (("Goal" :induct (first-taxon x))))

(defthm member-equal-first-taxon-orderly-cons-or
  (implies (and (member-equal (first-taxon x)
                              (get-taxa-from-order order))
                (member-equal (first-taxon y)
                              (get-taxa-from-order order))
                (good-order-list order))
           (or (equal (first-taxon (orderly-cons x y order))
                      (first-taxon x))
               (equal (first-taxon (orderly-cons x y order))
                      (first-taxon y))))
  :rule-classes nil)

(defthm member-equal-first-taxon-orderly-cons
  (implies (and (good-order-list order)
                (subset x (get-taxa-from-order order))
                (subset y (get-taxa-from-order order))
                (member-equal (first-taxon p) x)
                (member-equal (first-taxon q) y))
           (member-equal
            (first-taxon (orderly-cons p q order))
            (append x y)))
  :hints (("Subgoal *1/3.1'''" :use
           (:instance member-equal-first-taxon-orderly-cons-or
                      (x p)
                      (y q)))))


;leave here
(defthmd not-consp-difference-subset
  (implies (and (consp top)
                (true-listp top)
                (not (consp (difference top x))))
           (subset top x))
  :rule-classes :forward-chaining)


(defthm good-fringes-list-subsets
  (implies (good-fringes-list x)
           (good-fringes-list (get-subsets y x))))

(defthm good-fringes-list-non-subsets
  (implies (good-fringes-list x)
           (good-fringes-list (get-non-subsets y x))))


(defthm good-fringes-list-append
  (implies (and (good-fringes-list x)
                (good-fringes-list y))
           (good-fringes-list (append x y))))

; leave here
(defthm orderly-cons-nil
  (implies (and (good-order-list order)
                (member-equal (first-taxon x)
                              (get-taxa-from-order order)))
           (equal (orderly-cons x nil order)
                  (list x))))

(defthm first-taxon-parts-member-top
  (implies (and (subset-list under top)
                (no-conflicts-list under)
                (good-fringes-list under)
                (true-listp top)
                (consp top)
                (subset top (get-taxa-from-order order))
                (good-order-list order))
           (member-equal
            (first-taxon (partstotaspi top under order))
            top))
  :hints (("Goal" :induct (partstotaspi top under order))
          ("Subgoal *1/1.7'''" ;:in-theory
           ;(disable not-consp-difference-subset)
           :use (:instance not-consp-difference-subset
                           (x under1)))
          ("Subgoal *1/1.9''" :in-theory
           (disable member-equal-first-taxon-orderly-cons)
           :use
           (:instance member-equal-first-taxon-orderly-cons
                      (x under1)
                      (y (difference top under1))
                      (p (partstotaspi under1 (get-subsets under1 under2)
                                           order))
                      (q (partstotaspi (difference top under1)
                                           (get-non-subsets under1 under2)
                                           order))))))


(defthm smaller-member-smaller-firsts
  (implies (and (member-equal (first-taxon z) y)
                (not (consp x))
                (smaller-all x y order))
           (< (cdr (assoc-equal (first-taxon x) order))
              (cdr (assoc-equal (first-taxon z)
                                order)))))

;keep here
(defthm ordered-less-first-smaller-all
  (implies (and (ordered-taspi y order)
                (taspip nil y)
                (good-order-list order)
                (< (cdr (assoc-equal x order))
                   (cdr (assoc-equal (first-taxon y) order))))
           (smaller-all x (mytips y) order))
  :hints (("Goal" :in-theory (enable smaller-all))))


(defthmd helper
  (implies (and (subset fringes1 ofringe)
                (not (consp x))
                (member-equal
                 (first-taxon
                  (partstotaspi
                   fringes1
                   (get-subsets fringes1 fringes2) order))
                 fringes1)
                (smaller-all x ofringe order)
                (good-order-list order))
           (<=
            (cdr (assoc-equal (first-taxon x) order))
            (cdr
             (assoc-equal
              (first-taxon (partstotaspi fringes1 (get-subsets fringes1 fringes2)
                                         order))
              order))
            ))
  :hints (("Goal" :in-theory
           (disable smaller-member-smaller-firsts
                    smaller-member-smaller)
           :use (:instance smaller-member-smaller-firsts
                           (z (partstotaspi
                               fringes1
                               (get-subsets fringes1 fringes2) order))
                           (y ofringe))))
           )

(defthmd disjoint-parts-cons-gen
  (implies (and (not (member-equal x ofringe))
                (no-conflicts-list fringes)
                (smaller-all x ofringe order)
                (good-fringes-list fringes)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (member-equal x (get-taxa-from-order order))
                (subset-list fringes ofringe)
                (subset ofringe (get-taxa-from-order order))
                )
           (equal (partstotaspi (cons x ofringe)
                                fringes
                                order)
                  (cons x
                        (partstotaspi ofringe
                                      fringes
                                      order))))
  :hints (("Goal" :induct (partstotaspi ofringe fringes order)
           :expand (partstotaspi (cons x ofringe)
                                 (cons fringes1 fringes2)
                                 order))
          ("Subgoal *1/1.6.2''" :use
           (:instance helper))
          ("Subgoal *1/1.6.1''" :use
           (:instance helper))
          ))

(defthm consp-ofringe-from-consp-taspip
  (implies (and (consp x)
                (good-order-list order)
                (subset (mytips x)
                        (get-taxa-from-order order))
                (taspip flg x))
           (consp (ofringe flg x order))))

(defthm good-fringes-list-fringes
  (implies (and (subset (mytips x)
                        (get-taxa-from-order order))
                (taspip flg x)
                (good-order-list order))
           (good-fringes-list (fringes flg x order))))

(defthm disjoint-parts-cons
  (implies (and (not (member-equal x1 (mytips x2)))
                (< (cdr (assoc-equal x1 order))
                   (cdr (assoc-equal (first-taxon x2) order)))
                (good-order-list order)
                (no-duplicatesp-equal (mytips x2))
                (ordered-taspi x2 order)
                (no-duplicatesp-equal (strip-cdrs order))
                (member-equal x1 (get-taxa-from-order order))
                (subset (mytips x2)
                        (get-taxa-from-order order))
                (taspip nil x2))
           (equal (partstotaspi (cons x1 (ofringe nil x2 order))
                                (fringes nil x2 order)
                                order)
                  (cons x1
                        (partstotaspi (ofringe nil x2 order)
                                      (fringes nil x2 order)
                                      order))))
  :hints (("Goal" :use ((:instance disjoint-parts-cons-gen
                                   (ofringe (ofringe nil x2 order))
                                   (fringes (fringes nil x2 order))
                                   (x x1))
                        (:instance subset-ofringe-mytips
                                   (flg nil)
                                   (x x2))))
))

(defthm omerge-becomes-cons
  (implies (and (not (member-equal x1 (mytips x2)))
                (< (cdr (assoc-equal x1 order))
                   (cdr (assoc-equal (first-taxon x2) order)))
                (good-order-list order)
                (ordered-taspi x2 order)
                (no-duplicatesp-equal (strip-cdrs order))
                (member-equal x1 (get-taxa-from-order order))
                (subset (mytips x2)
                        (get-taxa-from-order order))
                (taspip nil x2))
           (equal (omerge (list x1)
                          (ofringe nil x2 order)
                          order)
                  (cons x1 (ofringe nil x2 order))))
  :hints (("Goal"
           :use (:instance smaller-all-omerge-becomes-cons
                           (y (ofringe nil x2 order))))
          ("Subgoal 2" :in-theory
           (disable ordered-less-first-smaller-all)
           :use ((:instance ordered-less-first-smaller-all
                           (y x2) (x x1))
                 (:instance subset-ofringe-mytips
                            (flg nil)
                            (x x2))))
          ("Subgoal 1" :use
           (:instance subset-ofringe-mytips
                            (flg nil)
                            (x x2)))
))

(defthm not-intersect-not-get-subsets
  (implies (and (not (intersect tips1 tips2))
                (good-fringes-list y)
                (subset-list y tips2)
                (subset z tips1))
           (not (get-subsets z y))))

(defthm get-subsets-append-simplification
  (implies (and (no-duplicatesp-equal
                 (append tips1 tips2))
                (true-listp x)
                (good-fringes-list y)
                (subset-list y tips2)
                (subset-list x z)
                (subset z tips1))
           (equal (get-subsets z (append x y))
                  x)))

(defthm get-non-subsets-append-simplification
  (implies (and (no-duplicatesp-equal
                 (append tips1 tips2))
                (true-listp x)
                (good-fringes-list y)
                (subset-list y tips2)
                (subset-list x z)
                (subset z tips1))
           (equal (get-non-subsets z (append x y))
                  y)))

(defthm no-duplicates-ofringe
  (implies (and (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (no-duplicatesp-equal (mytips x))
                (subset (mytips x)
                        (get-taxa-from-order order)))
           (no-duplicatesp-equal (ofringe flg x order)))
  :hints (("Subgoal *1/13.2''" :use
           ((:instance subset-ofringe-mytips
                       (flg nil)
                       (x x2))
            (:instance subset-ofringe-mytips
                       (flg nil)
                       (x x1))))
          ("Subgoal *1/13.1''" :use
           (:instance subset-ofringe-mytips
                       (flg nil)
                       (x x2))
            )
          ("Subgoal *1/13.1'4'" :in-theory
           (disable not-intersect-no-dups-no-dups-omerge)
           :use (:instance not-intersect-no-dups-no-dups-omerge
                           (x (list x1))
                           (y (ofringe nil x2 order))))

))

(defthm orderly-cons-becomes-cons
  (implies (and (ordered-taspi x order)
                (taspip nil x)
                (consp x)
                (taspip nil y)
                (ordered-taspi y order)
                (good-order-list order)
                (not (intersect (mytips x) (mytips y)))
                (< (cdr (assoc-equal (first-taxon x) order))
                   (cdr (assoc-equal (first-taxon y) order)))
                (subset (mytips x)
                        (get-taxa-from-order order))
                )
           (equal (orderly-cons x y order)
                  (cons x y)))
  :hints (("Goal" :induct (orderly-cons x y order))))


(defthm inductive-step-nil
   (implies (and (equal (partstotaspi (ofringe nil x1 order)
                                      (cdr (fringes t x1 order))
                                      order)
                        x1)
                 (equal (partstotaspi (ofringe nil x2 order)
                                      (fringes nil x2 order)
                                      order)
                        x2)
                 (< (cdr (assoc-equal (first-taxon x1) order))
                    (cdr (assoc-equal (first-taxon x2) order)))
                 (ordered-taspi x1 order)
                 (ordered-taspi x2 order)
                 (good-order-list order)
                 (no-duplicatesp-equal (strip-cdrs order))
                 (no-duplicatesp-equal (append (mytips x1) (mytips x2)))
                 (subset (append (mytips x1) (mytips x2))
                         (get-taxa-from-order order))
                 (consp x1)
                 (taspip nil x1)
                 (taspip nil x2)
                 (consp (fringes t x1 order)))
            (equal (partstotaspi (omerge (ofringe nil x1 order)
                                         (ofringe nil x2 order)
                                         order)
                                 (cons (ofringe nil x1 order)
                                       (append (cdr (fringes t x1 order))
                                               (fringes nil x2 order)))
                                 order)
                   (cons x1 x2)))
   :hints (("Goal" :do-not '(fertilize)
            :do-not-induct t
            :expand (partstotaspi (omerge (ofringe nil x1 order)
                                          (ofringe nil x2 order)
                                          order)
                                  (cons (ofringe nil x1 order)
                                        (append (cdr (fringes t x1 order))
                                                (fringes nil x2 order)))
                                  order))
           ("Goal'" :in-theory
            (disable get-subsets-append-simplification)
            :use (:instance get-subsets-append-simplification
                            (tips1 (mytips x1)) (tips2 (mytips x2))
                            (x (cdr (fringes t x1 order)))
                            (y (fringes nil x2 order))
                            (z (ofringe nil x1 order))))
           ("Subgoal 4" :in-theory
            (disable subset-list-fringes-ofringe)
            :use
            ((:instance subset-list-fringes-ofringe
                        (x x2)
                        (flg nil)
                        (flg2 nil))
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x2))))
           ("Subgoal 3" :use
            (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x1)))
           ("Subgoal 2" :in-theory
            (disable subset-list-fringes-ofringe)
            :use
            ((:instance subset-list-fringes-ofringe
                        (x x1)
                        (flg t)
                        (flg2 nil))
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x1))))
           ("Subgoal 1" :in-theory (disable difference-omerge)
            :use
            (:instance difference-omerge
                       (x (ofringe nil x1 order))
                       (y (ofringe nil x2 order))))
           ("Subgoal 1.4" :use
            ((:instance subset-ofringe-mytips
                        (flg nil)
                        (x x1))
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x2))))
           ("Subgoal 1.3" :use
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x2)))
           ("Subgoal 1.2" :use
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x1)))
           ("Subgoal 1.1" :in-theory
            (disable get-non-subsets-append-simplification)
            :use (:instance get-non-subsets-append-simplification
                            (tips1 (mytips x1)) (tips2 (mytips x2))
                            (x (cdr (fringes t x1 order)))
                            (y (fringes nil x2 order))
                            (z (ofringe nil x1 order))))
           ("Subgoal 1.1.3" :in-theory
            (disable subset-list-fringes-ofringe)
            :use ((:instance subset-list-fringes-ofringe
                             (flg nil)
                             (flg2 nil)
                             (x x2))
                  (:instance subset-ofringe-mytips
                             (flg nil)
                             (x x2))))
           ("Subgoal 1.1.2" :use
             (:instance subset-ofringe-mytips
                        (flg nil)
                        (x x1)))
           ("Subgoal 1.1.1" :in-theory
            (disable subset-list-fringes-ofringe)
            :use ((:instance subset-list-fringes-ofringe
                             (flg t)
                             (flg2 nil)
                             (x x1))
                  (:instance subset-ofringe-mytips
                             (flg nil)
                             (x x1))))
           ))

(defthm the-whole-shebang
  (implies (and (ordered-taspi x order)
                (good-order-list order)
                (not (and flg
                          (not (consp x))))
                (no-duplicatesp-equal
                 (strip-cdrs order))
                (no-duplicatesp-equal (mytips x))
                (subset (mytips x)
                        (get-taxa-from-order order))
                (taspip flg x))
           (if flg
               (equal (partstotaspi (car (fringes flg x order))
                                    (cdr (fringes flg x order))
                                    order)
                      x)
             (equal (partstotaspi (ofringe flg x order)
                                  (fringes flg x order)
                                  order)
                    x)))
  :hints (("Goal" :induct (fringes flg x order)))
  :rule-classes nil)

(defthm the-case-I-wanted
  (implies (and (ordered-taspi x order)
                (good-order-list order)
                (consp x)
                (no-duplicatesp-equal
                 (strip-cdrs order))
                (no-duplicatesp-equal (mytips x))
                (subset (mytips x)
                        (get-taxa-from-order order))
                (taspip t x))
           (equal (partstotaspi (car (fringes t x order))
                                (cdr (fringes t x order))
                                order)
                  x))
  :hints (("Goal" :use (:instance the-whole-shebang
                                  (flg t)))))

