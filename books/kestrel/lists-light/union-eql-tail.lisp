; Tail-recursive union using eql as the test
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also union$.

;; Add items from LST1 to ACC if they are not in LST2.
;this keeps acc separate (instead of extending lst2) so it will be fast if lst2 is small
(defun union-eql-tail-aux (lst1 lst2 acc)
  (declare (xargs :guard (and (if (eqlable-listp lst1)
                                  (true-listp lst2)
                                (and (true-listp lst1)
                                     (eqlable-listp lst2))))))
  (cond ((endp lst1) acc)
        ((member (car lst1) lst2)
         (union-eql-tail-aux (cdr lst1) lst2 acc))
        (t (union-eql-tail-aux (cdr lst1) lst2 (cons (car lst1) acc)))))

;; Union together LST1 and LST2, using EQL as the comparison.
;doesn't remove dups within either argument
(defun union-eql-tail (lst1 lst2)
  (declare (xargs :guard (and (if (eqlable-listp lst1)
                                  (true-listp lst2)
                                (and (true-listp lst1)
                                     (eqlable-listp lst2))))))
  (union-eql-tail-aux lst1 lst2 lst2))
