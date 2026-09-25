; Making a conjunction from a list of conjuncts
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the built-in function conjoin.  It handles T and NIL specially but
;; does not preserve EQUAL, only IFF (e.g., (conjoin (list ''3 ''t)) gives '3).
(defund make-conjunction-from-list (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      *t*
    (if (endp (rest lst))
        (first lst)
      `(if ,(first lst)
           ,(make-conjunction-from-list (rest lst))
         'nil))))

(defthm pseudo-termp-of-make-conjunction-from-list
  (implies (pseudo-term-listp lst)
           (pseudo-termp (make-conjunction-from-list lst)))
  :hints (("Goal" :in-theory (enable make-conjunction-from-list))))
