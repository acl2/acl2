; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "internal/subset-defs")
(include-book "set-defs")
(include-book "in-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod: Two necessary additions because of verify-guards fix, 9/19/2026.
; Perhaps these could std::defredundant could be improved to make these
; unnecessary.

(DEFUN-SK SUBSET-SK (X Y)
  (DECLARE (XARGS :VERIFY-GUARDS NIL))
  (DECLARE (XARGS :GUARD T))
  (FORALL (ELEM)
          (NON-EXEC (IMPLIES (IN ELEM X) (IN ELEM Y))))
  :REWRITE
  (IMPLIES (SUBSET-SK X Y)
           (NON-EXEC (IMPLIES (IN ELEM X) (IN ELEM Y))))
  :SKOLEM-NAME SUBSET-SK-WITNESS
  :THM-NAME SUBSET-SK-NECC)

(verify-guards SUBSET-SK)

(std::defredundant
  :names (subset
          subset$inline
          subset-sk-witness
          subset-sk
          subset-=
          subset-eq
          subset-eql
          ))
