; A simple function to append a list of lists all together
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also [books]/std/lists/flatten.lisp

;; Similar to flatten but more lightweight and has a stronger guard
(defund append-all (xs)
  (declare (xargs :guard (true-list-listp xs)))
  (if (endp xs)
      nil
    (append (first xs) (append-all (rest xs)))))

(defthm true-listp-of-append-all
  (implies (true-list-listp x)
           (true-listp (append-all x)))
  :hints (("Goal" :in-theory (enable append-all))))
