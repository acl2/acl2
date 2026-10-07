; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "internal/submap-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod: Two necessary additions because of verify-guards fix, 9/19/2026.
; Perhaps these could std::defredundant could be improved to make these
; unnecessary.

(DEFUN-SK SUBMAP-SK (X Y)
  (DECLARE (XARGS :VERIFY-GUARDS NIL))
  (DECLARE (XARGS :GUARD T))
  (FORALL
   (KEY DEFAULT)
   (NON-EXEC
    (IMPLIES (TREESET::IN KEY (KEYS X))
             (EQUAL (LOOKUP KEY X :DEFAULT DEFAULT)
                    (LOOKUP KEY Y :DEFAULT DEFAULT)))))
  :REWRITE
  (IMPLIES
   (SUBMAP-SK X Y)
   (NON-EXEC
    (IMPLIES (TREESET::IN KEY (KEYS X))
             (EQUAL (LOOKUP KEY X :DEFAULT DEFAULT)
                    (LOOKUP KEY Y :DEFAULT DEFAULT)))))
  :SKOLEM-NAME SUBMAP-SK-WITNESS
  :THM-NAME SUBMAP-SK-NECC)

(verify-guards SUBMAP-SK)

(std::defredundant
  :names (submap
          submap$inline
          submap-sk-witness
          submap-sk
          submap-=
          submap-eq
          submap-eql
          ))
