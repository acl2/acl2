; Additions to osets
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Clean this up

;;; This book brings in std/osets and some additional stuff from coi/osets.  It
;;; then adds more theorems about osets.

(include-book "std/osets/top" :dir :system)
(include-book "coi/osets/sets" :dir :system) ;include less? ;for set::emptyset
(include-book "kestrel/utilities/equal-of-booleans" :dir :system)

(in-theory (disable set::double-containment-expensive)) ;bad rule!  can introduce set reasoning out of nowhere
(local (in-theory (enable set::double-containment-expensive)))

(in-theory (disable set::sets-are-true-lists-cheap)) ;bad rule!  can introduce set reasoning out of nowhere

(defthm difference-when-subset
  (implies (set::subset x y)
           (equal (set::difference x y)
                  (set::emptyset)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable set::empty set::sfix))))

(defthm difference-self
  (equal (set::difference x x)
         (set::emptyset))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable set::empty set::sfix))))

(defthm intersect-difference-same
  (implies (and (set::setp s1)
                (set::setp s2))
           (equal (set::intersect s1 (set::difference s1 s2))
                  (set::difference s1 s2))))

(defthm difference-difference-same
  (implies (and (set::setp s1)
                (set::setp s2))
           (equal (set::difference s2 (set::difference s1 s2))
                  s2)))

(defthm union-of-difference-same
  (implies (and (set::setp s1)
                (set::setp s2))
           (equal (set::union s2
                              (set::difference s1 s2))
                  (set::union s2
                              s1))))

(defthm difference-of-union-same
  (implies (and (set::setp s1)
                (set::setp s2))
           (equal (set::difference (set::union s2 s1)
                                   s2)
                  (set::difference s1
                                   s2))))

(defun make-set-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      (cons 'set::insert
            (cons (car lst)
                  (cons (make-set-macro (cdr lst)) nil)))
      '(set::emptyset)
      ))

;a set analogue of "list"
(defmacro make-set (&rest args)
                       "Documentation available via :doc"
                       (make-set-macro args))

;;;;
(in-theory (disable set::in set::subset len set::union))


(defthm difference-of-union-of-difference-same
  (implies (and (set::setp s1)
                (set::setp s2)
                (set::setp s3))
           (equal (set::difference (set::union s3 s1) (set::difference s2 s3))
                  (set::union s3 (set::difference s1 s2)))))

(defthm intersect-difference-difference-same
  (implies (and (set::setp s1)
                (set::setp s2)
                (set::setp s3))
           (equal (set::intersect (set::difference s2 s3) (set::difference s2 (set::difference s1 s3)))
                  (set::intersect (set::difference s2 s3) (set::difference s2 s1)))))


(defthm intersect-difference-difference-same-alt
  (implies (and (set::setp s1)
                (set::setp s2)
                (set::setp s3))
           (equal (set::intersect (set::difference s2 s3) (set::intersect (set::difference s2 (set::difference s1 s3)) s4))
                  (set::intersect s4 (set::intersect (set::difference s2 s3) (set::difference s2 s1))))))

(defthm difference-of-union-difference-same
  (implies (and (set::setp s1)
                (set::setp s2)
                (set::setp s3))
           (equal (set::difference
                   (set::union
                    s3
                    s0)
                   (set::difference
                    s1
                    s0))
                  (set::union s0 (set::difference s3 s1)))))

;helps get rid of nested difference
(defthm difference-of-difference
  (equal (set::difference s1 (set::difference s2 s3))
         (set::union (set::intersect s1 s3)
                     (set::difference s1 s2))))

;when upgrading acl2 to a version that uses std as the core of coi:
(local (in-theory (enable set::pick-a-point-subset-strategy)))
;(local (in-theory (disable set::never-in-empty)))

;would like a pick-a-point-proof-strategy for empty
(defthm helper
  (set::subset (set::intersect (set::difference s1 s0)
                               (set::difference s0 s1))
               (set::emptyset))
  :hints (("Goal" :in-theory (e/d (;set::difference
                                                                      )
                                  (set::never-in-empty
                                   set::empty-subset-2)))))

(defthm intersect-difference-both-ways
  (equal (set::intersect (set::difference s1 s0)
                         (set::difference s0 s1))
         (set::emptyset))
  :hints (("Goal" :in-theory (e/d (set::empty) ( helper))
           :use (:instance helper))))

(defthm union-with-difference-same
 (equal (set::union s1 (set::difference s1 s0))
        (set::sfix s1)))

(defthm union-with-difference-same-alt
  (equal (set::union s1 (set::union (set::difference s1 s0) s2))
         (set::union s1 s2)))

;pulls the difference up; is that what we want to do?
(defthm intersect-of-difference
  (equal (set::intersect (set::difference s2 s3) s1)
         (set::difference (set::intersect s2 s1) s3)))

(defthm intersect-of-difference-alt
  (equal (set::intersect s1 (set::difference s2 s3))
         (set::difference (set::intersect s2 s1) s3)))

(defthm diffence-of-union-lemma
  (implies (set::empty (set::difference s1 s3))
           (equal (set::difference (set::union s1 s2) s3)
                  (set::difference s2 s3))))

(defthm diffence-of-union-lemma-alt
  (implies (set::empty (set::difference s1 s3))
           (equal (set::difference (set::union s2 s1) s3)
                  (set::difference s2 s3))))

(defthm subset-of-difference-1
  (equal (set::subset (set::difference s1 s2) s2)
         (set::subset s1 s2)))

(defthm union-intersect-self-one
  (equal (set::union s0 (set::intersect s1 s0))
         (set::sfix s0)))

(defthm union-intersect-self-two
  (equal (set::union s0 (set::intersect s0 s1))
         (set::sfix s0)))

(defthm difference-of-union
  (equal (set::difference (set::union a b) c)
         (set::union (set::difference a c) (set::difference b c))))

(defthm difference-twice
  (equal (set::difference (set::difference s1 s0) s0)
         (set::difference s1 s0)))

(defthm helper--
  (implies (set::empty (set::difference s1 s3))
           (set::subset (set::difference (set::difference s1 s2) s3)
                        (set::emptyset)))
  :hints (("Goal" :in-theory (disable set::empty-subset-2))))

(defthm difference-empty-lemma
  (implies (set::empty (set::difference s1 s3))
           (equal (set::difference (set::difference s1 s2) s3)
                  (set::emptyset)))
  :hints (("Goal" :use (:instance helper--)
           :in-theory (disable helper--))))

(defthm difference-reorder
  (equal (set::difference (set::difference s1 s2) s3)
         (set::difference (set::difference s1 s3) s2))
  :rule-classes ((:rewrite :loop-stopper ((s2 s3)))))

;more cases?
(defthm subset-union-union-helper
 (implies (set::subset b c)
          (set::subset (set::union a b) (set::union c a))))

(defthm equal-equal-a-head-hack
  (implies (and (set::in a x)
                (not (set::in a (set::tail x))))
           (equal (equal a (set::head x))
                  t)))

(defthm set::subset-in-2-alt
  (implies (and (not (set::in a y))
                (set::subset x y))
           (not (set::in a x))))

(defthm subset-hack
  (implies (set::subset (set::union z x) y)
           (set::subset x y)))

(defthm insert-not-equal-delete
  (not (equal (set::insert ad x) (set::delete ad y))))

(defthmd head-not
  (implies (and (not (set::empty ad-set))
                (not (set::in ad ad-set)))
           (not (equal ad (set::head ad-set)))))

(defthm insert-if-insert ;bozo hack
 (equal (set::insert a (if test (set::insert a x) x))
        (set::insert a x)))

(defthm subset-insert-insert-helper
  (implies (set::subset x (set::insert a y))
           (set::subset (set::insert a x) (set::insert a y))))

(defthm insert-head-union-tail
  (implies (not (set::empty x))
           (equal (set::insert (set::head x) (set::union y (set::tail x)))
                  (set::union x y))))

;yuck?
(defthm in-of-if
  (equal (set::in a (if test tp ep))
         (if test (set::in a tp) (set::in a ep))))

(defthm subset-insert-helper
  (implies (set::subset x y)
           (set::subset x (set::insert a y))))

;bozo why does this arise?
(defthm subset-of-if
  (equal (set::subset x (if test tp ep))
         (if test (set::subset x tp)
           (set::subset x ep))))

(defthmd subset-singleton-hack
   (equal (set::subset x (set::insert a nil))
          (or (set::empty x)
              (equal x (make-set a))))
   :hints (("Goal" :in-theory (disable ;set::insert-never-empty
                                       ;set::map-subset-helper
                                       )
            :expand ((set::subset x (set::insert a nil))))))

(defthm subset-of-insert-irrel
  (implies (not (set::in a x))
           (equal (set::subset x (set::insert a y))
                  (set::subset x y)))
  :hints (("Goal" :in-theory (enable set::subset))))

(defthm subset-of-delete-irrel
  (implies (not (set::in a x))
           (equal (set::subset x (set::delete a y))
                  (set::subset x y)))
  :hints (("Goal" :in-theory (enable set::subset))))

(defthm insert-when-empty
  (implies (and (syntaxp (not (equal y ''nil)))
                (set::empty y))
           (equal (set::insert a y)
                  (set::insert a nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1))))

(defthm insert-iff
  (iff (set::insert a x)
       t)
  :hints (("Goal" :in-theory (enable set::insert))))

;move
(defthm singleton-equal-insert-into-nil-rewrite
  (equal (EQUAL (LIST a) (SET::INSERT a NIL))
         t)
  :hints (("Goal" :expand ((SET::INSERT a NIL)))))

(defthm subset-delete-delete
  (implies (set::subset dom dom2)
           (set::subset (set::delete start dom)
                        (set::delete start dom2))))

(defthm subset-union-difference-same
  (implies (set::setp x) ;drop? ;
           (equal (set::subset x (set::union (set::difference y x) z))
                  (set::subset x z))))

(defthm intersect-when-subset
  (implies (and (set::subset x y)
                (set::setp x)
                (set::setp y))
           (equal (set::intersect x y)
                  x)))

(defthm subset-of-intersect-same
  (implies (and (set::setp x) ;drop? ; ;
                (set::setp y))
           (equal (set::subset x (set::intersect y x))
                  (set::subset x y)))
  :hints (("Goal" :in-theory (e/d (set::intersect-symmetric)
                                  ( ;set::never-in-empty
                                   set::pick-a-point-subset-strategy
                                   set::intersect-subset-x
                                   set::intersect)))))

(defthm insert-does-nothing-rewrite
  (implies (set::setp set)
           (equal (equal (set::insert item set) set)
                  (set::in item set))))

(local (in-theory (disable (:induction set::insert))))

(defthm set-delete-insert
  (implies (not (equal x y))
           (equal (set::delete x (set::insert y set))
                  (set::insert y (set::delete x set)))))

(defthmd set-insert-delete
  (implies (not (equal x y))
           (equal (set::insert y (set::delete x set))
                  (set::delete x (set::insert y set)))))

(defthmd set-delete-insert-strong
  (equal (set::delete x (set::insert y set))
         (if (equal x y)
             (set::delete x set)
           (set::insert y (set::delete x set)))))

(defthmd set-insert-delete-strong
  (equal (set::insert x (set::delete y set))
         (if (equal x y)
             (set::insert x set)
           (set::delete y (set::insert x set)))))

;FIXME where should this stuff go?

;isn't this defined in some set conversions.lisp book?
(defun set::2list (set)
  (declare (type (satisfies set::setp) set))
  (if (set::empty set) nil
    (cons (set::head set)
	  (set::2list (set::tail set)))))

(defthm true-listp-2list
  (true-listp (set::2list set)))

(defun list::2set (list)
  (declare (xargs :guard t))
  (if (consp list)
      (set::insert (car list)
                   (list::2set (cdr list)))
    nil))

(defthm setp-2set
  (set::setp (list::2set list)))


;; (defthm in-of-2set
;;   (equal (set::in a (list::2set x))
;;          (list::memberp a x)))

(defthm in-of-2set
  (iff (set::in a (list::2set x))
       (member a x)))

;move
(defthm 2set-of-cons
  (equal (list::2set (cons a b))
         (set::insert a (list::2set b)))
  :hints (("Goal" :in-theory (enable list::2set))))

(defthm len-of-2list
  (implies (set::setp x)
           (equal (len (set::2list x))
                  (set::cardinality x)))
  :hints (("Goal" :in-theory (enable len))))

(defthm consp-of-2list
  (implies (set::setp set)
           (equal (consp (set::2list set))
                  (not (set::empty set)))))


(defthm set::mergesort-of-singleton
  (equal (set::mergesort (list fn))
         (set::insert fn nil))
  :hints (("Goal" :in-theory (enable set::mergesort))))

(defthm mergesort-of-append
  (equal (set::mergesort (append x y))
         (set::union (set::mergesort x)
                     (set::mergesort y)))
  :hints (("Goal" :in-theory (enable set::mergesort))))

(defthm subset-of-if-arg1
  (equal (set::subset (if test x y) z)
         (if test
             (set::subset x z)
           (set::subset y z))))
