; Tail-recursive union using eql as the test
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "subsetp-equal"))

;; See also union$.

;; Add items from LST1 to ACC if they are not in LST2.
;this keeps acc separate (instead of extending lst2) so it will be fast if lst2 is small
(defund union-eql-tail-aux (lst1 lst2 acc)
  (declare (xargs :guard (and (if (eqlable-listp lst1)
                                  (true-listp lst2)
                                (and (true-listp lst1)
                                     (eqlable-listp lst2))))))
  (cond ((endp lst1) acc)
        ((member (car lst1) lst2)
         (union-eql-tail-aux (cdr lst1) lst2 acc))
        (t (union-eql-tail-aux (cdr lst1) lst2 (cons (car lst1) acc)))))

(local
  (defthm union-eql-tail-aux-iff
    (implies (subsetp-equal lst2 acc)
             (iff (union-eql-tail-aux lst1 lst2 acc)
                  (or (consp lst1) acc)))
    :hints (("Goal" :in-theory (enable union-eql-tail-aux)))))

(local
  (defthm member-equal-of-union-eql-tail-aux
    (implies (subsetp-equal lst2 acc)
             (iff (member-equal a (union-eql-tail-aux lst1 lst2 acc))
                  (or (member-equal a acc)
                      (and (member-equal a lst1)
                           (not (member-equal a lst2))))))
    :hints (("Goal" :in-theory (enable union-eql-tail-aux)))))

;; Union together LST1 and LST2, using EQL as the comparison.
;doesn't remove dups within either argument
(defund union-eql-tail (lst1 lst2)
  (declare (xargs :guard (and (if (eqlable-listp lst1)
                                  (true-listp lst2)
                                (and (true-listp lst1)
                                     (eqlable-listp lst2))))))
  (union-eql-tail-aux lst1 lst2 lst2))

(defthm union-eql-tail-iff
  (iff (union-eql-tail lst1 lst2)
       (or (consp lst1) lst2))
  :hints (("Goal" :in-theory (enable union-eql-tail))))

(defthm member-qqual-of-union-eql-tail
  (iff (member-equal a (union-eql-tail lst1 lst2))
       (or (member-equal a lst1)
           (member-equal a lst2)))
  :hints (("Goal" :in-theory (enable union-eql-tail))))
