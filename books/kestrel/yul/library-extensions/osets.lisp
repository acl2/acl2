; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "kestrel/utilities/osets" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defruled intersect-of-union
  (equal (intersect a (union b c))
         (union (intersect a b)
                     (intersect a c)))
  :enable (double-containment
           pick-a-point-subset-strategy))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defruled subset-of-union-and-union
  (implies (and (subset a b)
                (subset c d))
           (subset (union a c)
                   (union b d)))
  :enable (pick-a-point-subset-strategy
           subset-in))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defrule subset-of-insert-same-when-subset
  (implies (subset x y)
           (subset (insert a x)
                   (insert a y)))
  :enable subset)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist list-notin (x set)
  :guard (and (true-listp x)
              (setp set))
  (not (in x set))
  :true-listp nil
  :elementp-of-nil :unknown
  ///

  (std::defrule list-notin-of-sfix-2
    (equal (list-notin list (sfix set))
           (list-notin list set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::define list-insert ((l true-listp) (s setp))
  :returns (new-s setp)
  (cond ((endp l) (sfix s))
        (t (list-insert (cdr l) (insert (car l) s))))
  ///

  (std::defrule subset-of-list-insert
    (subset s (list-insert l s))
    :rule-classes (:rewrite
                   (:forward-chaining :trigger-terms ((list-insert l s)))))

  (in-theory (disable (:forward-chaining subset-of-list-insert)))

  (std::defrule in-of-list-insert
    (iff (in elem (list-insert list set))
         (or (member-equal elem list)
             (in elem set)))
    :induct (list-insert list set))

  (std::defrule set-list-in-of-list-insert
    (list-in list (list-insert list set))
    :enable list-in)

  (std::defrule list-insert-of-append
    (equal (list-insert (append list1 list2) set)
           (list-insert list1 (list-insert list2 set))))

  (std::defrule list-insert-commutative
    (equal (list-insert list1 (list-insert list2 set))
           (list-insert list2 (list-insert list1 set))))

  (std::defrule subset-of-list-insert-same-when-subset
    (implies (subset x y)
             (subset (list-insert l x)
                     (list-insert l y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd subset-of-mergesort-and-mergesort
  (equal (subset (mergesort x) (mergesort y))
         (subsetp-equal x y))
  :hints (("Goal" :in-theory (enable mergesort))))
