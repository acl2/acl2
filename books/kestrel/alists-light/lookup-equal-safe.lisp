; Look up a key using EQUAL, throwing an error if not found.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "lookup-equal") ;; included because we rewrite lookup-equal-safe to lookup-equal

;; Looks up KEY in ALIST, using equal as the test.
;; Throws an error if KEY is not bound in ALIST.
(defund lookup-equal-safe (key alist)
  (declare (xargs :guard (alistp alist)))
  (let ((result (assoc-equal key alist)))
    (if result
        (cdr result)
      (er hard? 'lookup-equal-safe "There is no binding for key ~x0 in alist ~x1." key alist))))

;; For reasoning, we immediately turn lookup-equal-safe into lookup-equal.
(defthm lookup-equal-safe-becomes-lookup-equal
  (equal (lookup-equal-safe key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal-safe lookup-equal))))
