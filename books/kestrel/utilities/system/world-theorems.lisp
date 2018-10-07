; System Utilities -- Theorems about World-Related Functions
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc theorems-about-world-related-functions
  :parents (theorems-about-non-kestrel-books system-utilities-non-built-in)
  :short "Theorems about world-related functions defined outside the
          <see topic='@(url kestrel-books)'>Kestrel Books</see>."
  :long
  "@(def arity-iff)
   @(def plist-worldp-when-plist-worldp-with-formals-cheap)
   @(def alistp-of-getprops)")

(defthm arity-iff
  (iff (arity fn wrld)
       (or (consp fn)
           (function-symbolp fn wrld)))
  :hints (("Goal" :in-theory (enable arity))))

(defthm plist-worldp-when-plist-worldp-with-formals-cheap
  (implies (not (plist-worldp wrld))
           (not (plist-worldp-with-formals wrld)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm alistp-of-getprops
  (alistp (getprops key world-name w))
  :hints (("Goal" :in-theory (enable symbol-<))))
