; Look up a key using EQ, with a guard requiring it to be present
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also lookup-eq-safe

(include-book "lookup-equal")

;; A variant of lookup-eq that requires the key to exist in the alist (for
;; higher assurance).
(defund lookup-eq-required (key alist)
  (declare (xargs :guard (and (if (symbolp key)
                                  (alistp alist)
                                (symbol-alistp alist))
                              ;; key must be present:
                              (assoc-eq key alist))))
  ;; same as lookup-eq:
  (cdr (assoc-eq key alist)))

;; For reasoning, we immediately transform lookup-eq-required into lookup-equal
(defthm lookup-eq-required-becomes-lookup-equal
  (equal (lookup-eq-required key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-eq-required lookup-equal))))
