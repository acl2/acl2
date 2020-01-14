; The definition of reverse-list.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "reverse-list"))

;; All events in this books should be redundant (proofs were done in the book
;; included above).

(defund reverse-list (x)
  (declare (xargs :guard (true-listp x) ;new
                  :verify-guards nil ;done below
                  ))
  (mbe :logic (if (consp x)
                  (append (reverse-list (cdr x)) (list (car x)))
                nil)
       :exec (revappend x nil)))

(verify-guards reverse-list)
