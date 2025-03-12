; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "in-defs")
(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset
  ((x setp)
   (y setp))
  (declare (xargs :type-prescription (booleanp (subset x y))))
  :parents (set)
  :short "Check if one set is a subset of the other."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n\\log(m))$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n\\log(m/n))$), where
      @($n < m$). This may be implemented similar to @(tsee diff).)"))
  (or (emptyp x)
      (and (in (head x) y)
           (subset (left x) y)
           (subset (right x) y))))
