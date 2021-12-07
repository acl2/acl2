; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "kestrel/utilities/osets" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::define list-insert ((l true-listp) (s setp))
  :returns (new-s setp)
  (cond ((endp l) (sfix s))
        (t (list-insert (cdr l) (insert (car l) s))))
  ///

  (std::defrule subset-of-list-insert
    (subset s (list-insert l s)))

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
           (list-insert list2 (list-insert list1 set)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defruled intersect-of-union
  (equal (intersect a (union b c))
         (union (intersect a b)
                     (intersect a c)))
  :enable (double-containment
           pick-a-point-subset-strategy))
