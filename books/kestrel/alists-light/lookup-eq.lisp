; Lookup a key in an alist using EQ
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

(include-book "lookup-equal") ;; included becase we rewrite lookup-eq to lookup-eqal

;; Look up KEY in ALIST, using eq as the test.
(defund lookup-eq (key alist)
  (declare (xargs :guard (if (symbolp key)
                             (alistp alist)
                           (symbol-alistp alist))))
  (cdr (assoc-eq key alist)))

;; Our strategy will be to rewrite lookup-eq to lookup-equal.
(defthm lookup-eq-becomes-lookup-equal
  (equal (lookup-eq key alist)
         (lookup-equal key alist))
  :hints (("Goal" :in-theory (enable lookup-equal lookup-eq))))
