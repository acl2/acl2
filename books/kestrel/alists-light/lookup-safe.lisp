; Look up a key using EQL, throwing an error if not found.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-equal") ;; included because we rewrite lookup-safe to lookup-equal

;; Looks up KEY in ALIST, using eql as the test (like assoc and lookup).
;; Throws an error if KEY is not bound in ALIST.
(defund lookup-safe (key alist)
  (declare (xargs :guard (if (eqlablep key)
                             (alistp alist)
                           (eqlable-alistp alist))))
  (let ((result (assoc key alist)))
    (if result
        (cdr result)
      (er hard? 'lookup-safe "There is no binding for key ~x0 in alist ~x1." key alist))))

;; For reasoning, we immediately turn lookup-safe into lookup-equal.
(defthm lookup-safe-becomes-lookup-equal
  (equal (lookup-safe key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-safe lookup-equal))))
