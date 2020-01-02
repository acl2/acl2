; A utility to remove duplicates, keeping the first of each set
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund remove-duplicates-equal$-aux (lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              (true-listp acc))))
  (if (endp lst)
      (reverse acc)
    (if (member-equal (first lst) acc)
        (remove-duplicates-equal$-aux (rest lst) acc) ;drop it
      (remove-duplicates-equal$-aux (rest lst) (cons (first lst) acc)))))

;; Like remove-duplicates-equal but keeps the first, rather than the
;; last, element of each set of duplicates.
(defund remove-duplicates-equal$ (lst)
  (declare (xargs :guard (true-listp lst)))
  (remove-duplicates-equal$-aux lst nil))

(defthm true-listp-of-remove-duplicates-equal$-aux
  (implies (true-listp acc)
           (true-listp (remove-duplicates-equal$-aux lst acc)))
  :hints (("Goal" :in-theory (enable remove-duplicates-equal$-aux))))

(defthm true-listp-of-remove-duplicates-equal$
  (true-listp (remove-duplicates-equal$ lst))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable remove-duplicates-equal$))))
