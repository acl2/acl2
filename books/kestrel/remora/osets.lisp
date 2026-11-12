; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Stephen Westfold
;          Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)

(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ osets
  :parents (library-extensions)
  :short "Library extensions for osets."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ list-to-oset (l)
  :short "Converts a list to an oset by sorting and removing dupliates."
  `(set::mergesort ,l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled mergesort-of-cons
  (equal (set::mergesort (cons a l))
         (set::insert a (set::mergesort l)))
  :enable set::mergesort)

;;;;;;;;;;;;;;;;;;;;

(defruled mergesort-when-consp
  (implies (consp l)
           (equal (set::mergesort l)
                  (set::insert (car l) (set::mergesort (cdr l)))))
  :enable mergesort-of-cons)

;;;;;;;;;;;;;;;;;;;;

(defruled mergesort-when-singleton
  (implies (and (consp l)
                (not (consp (cdr l))))
           (equal (set::mergesort l)
                  (set::insert (car l) nil)))
  :expand ((set::mergesort l)
           (set::mergesort (cdr l))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled union-of-differences
  (equal (set::union (set::difference a c) (set::difference b c))
         (set::difference (set::union a b) c))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;

(defruled union-difference-nest-identity
  :short "Rearrangement of a nested union and difference,
          as arises for the free variables of sequential binders."
  (equal (set::union f1
                     (set::difference (set::union f2 (set::difference fb b2))
                                      b1))
         (set::union f1
                     (set::union (set::difference f2 b1)
                                 (set::difference fb (set::union b1 b2)))))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;

(defruled difference-of-nil-right
  (equal (set::difference x nil)
         (set::sfix x))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled emptyp-intersect-of-union-left-1
  (implies (set::emptyp (set::intersect (set::union a b) c))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (set::x (set::intersect a c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::union a b)
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-of-union-left-2
  (implies (set::emptyp (set::intersect (set::union a b) c))
           (set::emptyp (set::intersect b c)))
  :use ((:instance set::in-head (set::x (set::intersect b c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::union a b)
                                           c))))
  :disable set::in-head)

(defruled not-in-when-emptyp-intersect-of-insert
  (implies (set::emptyp (set::intersect (set::insert k s) b))
           (not (set::in k b)))
  :use ((:instance set::never-in-empty
                   (set::a k)
                   (set::x (set::intersect (set::insert k s)
                                           b)))))

(defruled emptyp-intersect3-binder-union
  (implies (set::emptyp
            (set::intersect (set::union other (set::difference fvb p))
                            (set::intersect bound keys)))
           (set::emptyp
            (set::intersect fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
  :use ((:instance set::in-head
                   (set::x (set::intersect
                            fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect
                        fvb
                        (set::intersect bound
                                        (set::difference keys p)))))
                   (set::x (set::intersect (set::union other (set::difference fvb p))
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect3-binder-plain
  (implies (set::emptyp
            (set::intersect (set::difference fvb p)
                            (set::intersect bound keys)))
           (set::emptyp
            (set::intersect fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
  :use ((:instance set::in-head
                   (set::x (set::intersect
                            fvb
                            (set::intersect bound
                                            (set::difference keys p)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect
                        fvb
                        (set::intersect bound
                                        (set::difference keys p)))))
                   (set::x (set::intersect (set::difference fvb p)
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect3-binder-delete
  (implies (set::emptyp
            (set::intersect (set::union other (set::delete v fvb))
                            (set::intersect bound keys)))
           (set::emptyp
            (set::delete v
                         (set::intersect fvb
                                         (set::intersect bound keys)))))
  :use ((:instance set::in-head
                   (set::x (set::delete
                            v
                            (set::intersect fvb
                                            (set::intersect bound keys)))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::delete
                        v
                        (set::intersect fvb
                                        (set::intersect bound keys)))))
                   (set::x (set::intersect (set::union other (set::delete v fvb))
                                           (set::intersect bound keys)))))
  :disable set::in-head)

(defruled emptyp-intersect-singleton
  (equal (set::emptyp (set::intersect (set::insert name nil) c))
         (not (set::in name c)))
  :enable (set::intersect))

(defruled emptyp-intersect-of-insert-union-1
  (implies (set::emptyp
            (set::intersect (set::insert k (set::union a b)) c))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (set::x (set::intersect a c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::insert k (set::union a b))
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-of-insert-union-2
  (implies (set::emptyp
            (set::intersect (set::insert k (set::union a b)) c))
           (set::emptyp (set::intersect b c)))
  :use ((:instance set::in-head (set::x (set::intersect b c)))
        (:instance set::never-in-empty
                   (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::insert k (set::union a b))
                                           c))))
  :disable set::in-head)

(defruled emptyp-intersect-mono-right
  (implies (set::emptyp (set::intersect s bound))
           (set::emptyp (set::intersect s (set::intersect bound keys))))
  :use ((:instance set::in-head
                   (set::x (set::intersect s (set::intersect bound keys))))
        (:instance set::never-in-empty
                   (set::a (set::head
                       (set::intersect s (set::intersect bound keys))))
                   (set::x (set::intersect s
                                           bound))))
  :disable set::in-head)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Monotonicity of the operations with respect to containment.

(defruled intersect-subset-monotone
  :short "Intersection is monotone in both arguments."
  (implies (and (set::subset a a2)
                (set::subset b b2))
           (set::subset (set::intersect a b) (set::intersect a2 b2)))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defruled emptyp-of-intersect-when-subsets
  :short "Disjointness is inherited by subsets."
  (implies (and (set::subset a a2)
                (set::subset b b2)
                (set::emptyp (set::intersect a2 b2)))
           (set::emptyp (set::intersect a b)))
  :use ((:instance intersect-subset-monotone)
        (:instance set::emptyp-subset-2
                   (x (set::intersect a b))
                   (y (set::intersect a2 b2))))
  :disable set::emptyp-subset-2)

;;;;;;;;;;;;;;;;;;;;

(defruled subset-of-union-forward
  (implies (set::subset (set::union x y) z)
           (and (set::subset x z) (set::subset y z)))
  :enable (set::pick-a-point-subset-strategy set::subset-in set::union-in))

(defruled subset-of-union-backward
  (implies (and (set::subset x z) (set::subset y z))
           (set::subset (set::union x y) z))
  :enable (set::pick-a-point-subset-strategy set::subset-in set::union-in))

(defruled subset-of-union
  :short "A union is contained in a set iff both operands are."
  (equal (set::subset (set::union x y) z)
         (and (set::subset x z) (set::subset y z)))
  :use (subset-of-union-forward subset-of-union-backward))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lifting a containment through the operations that a set-valued fold
; applies to its recursive results: the operations that only grow the
; right-hand side, and those that only shrink the left-hand side.  These
; are collected in a ruleset, together with the splitting of a union on
; the left, since a fold's step needs them together: the step relates a
; union of recursive results to a union of larger ones.

(defruled subset-of-union-right-1
  (implies (set::subset x y)
           (set::subset x (set::union y z)))
  :use ((:instance set::subset-transitive (x x) (y y) (z (set::union y z)))))

(defruled subset-of-union-right-2
  (implies (set::subset x z)
           (set::subset x (set::union y z)))
  :use ((:instance set::subset-transitive (x x) (y z) (z (set::union y z)))))

(defruled subset-of-insert-right
  (implies (set::subset x y)
           (set::subset x (set::insert a y)))
  :use ((:instance set::subset-transitive (x x) (y y) (z (set::insert a y)))))

(defruled subset-of-delete-left
  (implies (set::subset x y)
           (set::subset (set::delete a x) y))
  :use ((:instance set::subset-transitive (x (set::delete a x)) (y x) (z y))))

(defruled subset-of-difference-left
  (implies (set::subset x y)
           (set::subset (set::difference x z) y))
  :use ((:instance set::subset-transitive
                   (x (set::difference x z)) (y x) (z y))))

(deftheory subset-lifting-rules
  '(subset-of-union
    subset-of-union-right-1
    subset-of-union-right-2
    subset-of-insert-right
    subset-of-delete-left
    subset-of-difference-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sorting a list into a set is monotone with respect to list containment.

(defruled subset-of-mergesort-when-subsetp-equal
  (implies (subsetp-equal x y)
           (set::subset (set::mergesort x) (set::mergesort y)))
  :enable (set::pick-a-point-subset-strategy
           set::in-mergesort
           acl2::member-equal-when-subsetp-equal-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Disjointness: its consequences for membership and difference, its
; monotonicity, and the containment of a sorted tail.

(defruled not-in-when-subset-and-not-in-super
  :short "Contrapositive of containment."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('set::subset-in-2') says the same thing and is always enabled,
     but its free-variable search has to find the containment in the
     context; this form is enabled where the containment is known and the
     conclusion is the goal."))
  (implies (and (set::subset x s)
                (not (set::in a s)))
           (not (set::in a x)))
  :use ((:instance set::subset-in (a a) (x x) (y s))))

(defruled not-in-when-disjoint
  (implies (and (set::emptyp (set::intersect y x))
                (set::in a x))
           (not (set::in a y)))
  :use ((:instance set::never-in-empty
                   (a a)
                   (x (set::intersect y x)))))

(defruled difference-when-disjoint
  (implies (and (set::setp x)
                (set::emptyp (set::intersect y x)))
           (equal (set::difference x y) x))
  :enable (set::double-containment
           set::pick-a-point-subset-strategy
           not-in-when-disjoint))

(defruled disjoint-monotone
  (implies (and (set::emptyp (set::intersect l x))
                (set::subset l2 l))
           (set::emptyp (set::intersect l2 x)))
  :use ((:instance set::in-head (x (set::intersect l2 x)))
        (:instance set::never-in-empty
                   (a (set::head (set::intersect l2 x)))
                   (x (set::intersect l x)))
        (:instance set::in-tail
                   (a (set::head (set::intersect l2 x)))
                   (x l2))
        (:instance set::subset-in
                   (a (set::head (set::intersect l2 x)))
                   (x l2)
                   (y l))))

(defruled subset-of-mergesort-of-cdr
  (set::subset (set::mergesort (cdr l)) (set::mergesort l))
  :enable (set::pick-a-point-subset-strategy))

(defruled subset-of-delete-when-subset
  (implies (set::subset s f)
           (set::subset (set::delete n s) (set::delete n f)))
  :enable (set::pick-a-point-subset-strategy
           set::delete-in
           set::subset-in))

(defruled not-in-when-subset-of-union
  (implies (and (set::subset b (set::union u1 u2))
                (not (set::in x u1))
                (not (set::in x u2)))
           (not (set::in x b)))
  :enable set::union-in
  :use ((:instance set::subset-in (a x) (x b) (y (set::union u1 u2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; More facts about sets, and about sets as lists, gathered from the proofs
; about lambda lifting.

(local (include-book "std/lists/sets" :dir :system))

(defruled emptyp-intersect-of-union-left
  (implies (and (set::emptyp (set::intersect a c))
                (set::emptyp (set::intersect b c)))
           (set::emptyp (set::intersect (set::union a b) c)))
  :use ((:instance set::in-head (x (set::intersect (set::union a b) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::union a b) c)))
                   (set::x (set::intersect a c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::union a b) c)))
                   (set::x (set::intersect b c)))))

(defruled emptyp-intersect-when-subset-right
  (implies (and (set::emptyp (set::intersect a c1))
                (set::subset c c1))
           (set::emptyp (set::intersect a c)))
  :use ((:instance set::in-head (x (set::intersect a c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect a c1)))
        (:instance set::subset-in (set::a (set::head (set::intersect a c)))
                   (set::x c) (set::y c1))))

(defruled emptyp-intersect-of-insert-left
  (implies (and (not (set::in x c))
                (set::emptyp (set::intersect a c)))
           (set::emptyp (set::intersect (set::insert x a) c)))
  :use ((:instance set::in-head (x (set::intersect (set::insert x a) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect (set::insert x a) c)))
                   (set::x (set::intersect a c)))))

(defruled emptyp-of-intersect-of-union
  (equal (set::emptyp (set::intersect (set::union a b) c))
         (and (set::emptyp (set::intersect a c))
              (set::emptyp (set::intersect b c))))
  :use (emptyp-intersect-of-union-left
        (:instance set::in-head (x (set::intersect a c)))
        (:instance set::in-head (x (set::intersect b c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect a c)))
                   (set::x (set::intersect (set::union a b) c)))
        (:instance set::never-in-empty (set::a (set::head (set::intersect b c)))
                   (set::x (set::intersect (set::union a b) c)))))

(defruled subsetp-of-union-mergesort-append
  (implies (set::setp s)
           (subsetp-equal (set::union (set::mergesort l) s) (append l s)))
  :enable set::in-to-member
  :use ((:instance set::in-to-member
                   (a (acl2::subsetp-witness (set::union (set::mergesort l) s)
                                             (append l s)))
                   (x (set::union (set::mergesort l) s)))))

(defruled subsetp-of-insert-cons
  (implies (set::setp s)
           (subsetp-equal (set::insert a s) (cons a s)))
  :use ((:instance set::in-to-member
                   (a (acl2::subsetp-witness (set::insert a s) (cons a s)))
                   (x (set::insert a s)))))

(defruled subset-of-tail-when-subset
  (implies (set::subset x y)
           (set::subset (set::tail x) y))
  :use (:instance set::subset-transitive (x (set::tail x)) (y x) (z y)))

(defruled subset-of-difference-of-difference
  (implies (and (set::subset a b) (set::subset c d))
           (set::subset (set::difference a d) (set::difference b c)))
  :enable (set::subset-in set::pick-a-point-subset-strategy))

(defruled subset-of-difference-when-subset
  (implies (set::subset a b)
           (set::subset (set::difference a c) (set::difference b c))))

(defruled subsetp-equal-when-subset-of-set
  (implies (and (subsetp-equal l s1)
                (set::subset s1 s2)
                (set::setp s1)
                (set::setp s2))
           (subsetp-equal l s2))
  :enable (acl2::subsetp-witness-rw acl2::subsetp-member set::subset-in
           set::in-to-member)
  :use ((:instance set::subset-in
                   (a (acl2::subsetp-witness l s2)) (x s1) (y s2))))

(defruled difference-of-singleton-mergesort
  (implies (set::setp s)
           (equal (set::difference s (set::mergesort (list v)))
                  (set::delete v s)))
  :enable (set::double-containment set::pick-a-point-subset-strategy))

(defruled no-duplicatesp-equal-when-setp
  (implies (set::setp x)
           (no-duplicatesp-equal x))
  :induct (len x)
  :enable (len set::setp no-duplicatesp-equal member-equal)
  :expand ((set::setp x))
  :hints (("Subgoal *1/1"
           :use ((:instance set::not-member-when-smaller
                            (a (car x)) (x (cdr x)))))))

(defruled in-when-member-of-subsetp
  (implies (and (subsetp-equal l s)
                (member-equal e l)
                (set::setp s))
           (set::in e s))
  :enable (set::in-to-member acl2::subsetp-member))

(defruled car-cdr-of-nonempty-setp
  (implies (and (set::setp x) (not (set::emptyp x)))
           (and (equal (set::head x) (car x))
                (equal (set::tail x) (cdr x))))
  :enable (set::head set::tail set::emptyp))

(defruled not-emptyp-when-consp-setp
  (implies (and (set::setp x) (consp x))
           (not (set::emptyp x)))
  :enable set::emptyp)

(defruled subset-of-cdr-when-subset-setp
  (implies (and (set::setp x) (set::subset x y))
           (set::subset (cdr x) y))
  :use ((:instance subset-of-tail-when-subset)
        (:instance car-cdr-of-nonempty-setp))
  :cases ((set::emptyp x))
  :enable set::emptyp)

(defruled emptyp-when-not-consp-setp
  (implies (and (set::setp x) (not (consp x)))
           (set::emptyp x))
  :enable set::emptyp)

(defruled subsetp-of-union-mergesort-right
  (implies (and (subsetp-equal l s)
                (set::setp s))
           (subsetp-equal l (set::union (set::mergesort more) s)))
  :enable acl2::subsetp-member
  :use ((:instance set::in-to-member
                   (a
                    (acl2::subsetp-witness l
                                           (set::union (set::mergesort more)
                                                       s)))
                   (x s))
        (:instance set::in-to-member
                   (a
                    (acl2::subsetp-witness l
                                           (set::union (set::mergesort more)
                                                       s)))
                   (x (set::union (set::mergesort more) s)))))

(defruled union-of-emptyp-right
  (implies (and (set::setp x) (set::emptyp y))
           (equal (set::union x y) x)))

(defruled subset-of-difference-and-intersect-when-subset
  (implies (set::subset a b)
           (and (set::subset (set::difference a c) b)
                (set::subset (set::intersect a c) b)))
  :enable (set::pick-a-point-subset-strategy set::subset-in))

(defruled subset-of-insert-both
  (implies (set::subset x y)
           (set::subset (set::insert a x) (set::insert a y)))
  :enable set::subset-insert-x
  :use ((:instance set::subset-transitive (set::x x) (set::y y)
                   (set::z (set::insert a y)))))

(defruled in-insert-when-subset-delete
  (implies (and (set::subset (set::delete n a) u)
                (set::in x a))
           (set::in x (set::insert n u)))
  :use ((:instance set::subset-in
                   (set::a x) (set::x (set::delete n a)) (set::y u))))

(defruled subset-insert-when-subset-delete
  (implies (set::subset (set::delete n a) u)
           (set::subset a (set::insert n u)))
  :enable (set::pick-a-point-subset-strategy in-insert-when-subset-delete))

(defruled subsetp-equal-when-all-in
  (implies (and (set::setp s)
                (set::subset (set::mergesort l) s))
           (subsetp-equal l s))
  :induct (len l)
  :enable (len subsetp-equal member-equal set::in-to-member
           mergesort-of-cons)
  :hints (("Subgoal *1/1"
           :use ((:instance set::subset-in (set::a (car l))
                            (set::x (set::mergesort l)) (set::y s))))))
