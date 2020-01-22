; Look up a key using EQ, throwing an error if not found.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "lookup-equal")

;what about when the value is nil?
(defund lookup-eq-safe (key alist)
  (declare (xargs :guard (if (symbolp key)
                             (alistp alist)
                           (symbol-alistp alist))
                  :guard-hints (("Goal" :in-theory (enable alistp assoc-eq)))))
  (let ((result (assoc-eq key alist)))
    (if result
        (cdr result)
      (hard-error
       'lookup-eq-safe
       "There is no binding for key ~x0 in the alist ~x1.~%"
       (acons #\0 key (acons #\1 alist nil))))))

(defthm lookup-eq-safe-becomes-lookup-equal
  (equal (lookup-eq-safe key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-eq-safe lookup-equal))))
