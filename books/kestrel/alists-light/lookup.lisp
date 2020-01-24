; Lookup a key in an alist using EQL
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

(include-book "lookup-equal") ;; included becase we rewrite lookup to lookup-eqal

;; Look up KEY in ALIST, using eql as the test (like assoc).
(defund lookup (key alist)
  (declare (xargs :guard (if (eqlablep key)
                             (alistp alist)
                           (eqlable-alistp alist))))
  (cdr (assoc key alist)))

;; Our strategy will be to rewrite lookup to lookup-equal.
(defthm lookup-becomes-lookup-equal
  (equal (lookup key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal
                                     lookup))))
