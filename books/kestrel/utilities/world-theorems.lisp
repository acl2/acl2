; Theorems about World-Related Functions
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc theorems-about-world-related-functions
  :parents (theorems-about-non-kestrel-books)
  :short "Some theorems about world-related functions
          defined outside the Kestrel Books."
  :long
  "@(def arity-iff)
   @(def plist-worldp-when-plist-worldp-with-formals-cheap)")

(defthm arity-iff
  (iff (arity fn wrld)
       (or (consp fn)
           (function-symbolp fn wrld)))
  :hints (("Goal" :in-theory (enable arity))))

(defthm plist-worldp-when-plist-worldp-with-formals-cheap
  (implies (not (plist-worldp wrld))
           (not (plist-worldp-with-formals wrld)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))
