; Look up a key using EQ, throwing an error if not found.
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

;; Looks up KEY in ALIST, using eq as the test (like assoc-eq and lookup-eq).
;; Throws an error if KEY is not bound in ALIST.
(defund lookup-eq-safe (key alist)
  (declare (xargs :guard (if (symbolp key)
                             (alistp alist)
                           (symbol-alistp alist))))
  (let ((result (assoc-eq key alist)))
    (if result
        (cdr result)
      (er hard? 'lookup-eq-safe "There is no binding for key ~x0 in alist ~x1." key alist))))

;; For reasoning, we immediately turn lookup-eq-safe into lookup-equal.
(defthm lookup-eq-safe-becomes-lookup-equal
  (equal (lookup-eq-safe key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-eq-safe lookup-equal))))
