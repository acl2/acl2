; BV Lists Library: bvnot-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop-list")
(include-book "kestrel/bv/defs-bitwise" :dir :system)
(local (include-book "kestrel/bv/bvnot" :dir :system))

;could use a defmap to define this
(defun bvnot-list (size lst)
  (declare (xargs :guard (and (natp size)
                              (all-integerp lst))))
  (if (atom lst)
      nil
    (cons (bvnot size (car lst))
          (bvnot-list size (cdr lst)))))

(defthm car-of-bvnot-list
  (equal (car (bvnot-list size lst))
         (if (consp lst)
             (bvnot size (car lst))
           nil)))

(defthm nth-of-bvnot-list
  (implies (and (natp n)
                (< n (len lst)))
           (equal (nth n (bvnot-list size lst))
                  (bvnot size (nth n lst))))
  :hints (("Goal" :in-theory (enable nth bvnot-list))))

(defthm len-of-bvnot-list
  (equal (len (bvnot-list width lst))
         (len lst)))

(defthm bvnot-list-of-bvnot-list
  (equal (bvnot-list size (bvnot-list size lst))
         (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvnot-list-of-bvchop-list
  (equal (bvnot-list size (bvchop-list size lst))
         (bvnot-list size lst)))
