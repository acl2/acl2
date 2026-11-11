; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "set-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "cardinality-defs")
(include-book "delete-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "generic-typed"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod: Necessary additions because of verify-guards fix, 9/19/2026.
; Perhaps these could std::defredundant could be improved to make these
; unnecessary.

(ENCAPSULATE (((GENERICP *) => *))
  (WITH-OUTPUT :OFF SUMMARY (LOGIC))
  (WITH-OUTPUT :SUMMARY-OFF
    (:OTHER-THAN ACL2::REDUNDANT)
    (LOCAL (DEFUN GENERICP (ACL2::X1)
             (DECLARE (IGNORE ACL2::X1))
             NIL))))

(DEFUN-SK SET-ALL-GENERICP-SK (SET)
  (DECLARE (XARGS :VERIFY-GUARDS NIL))
  (DECLARE (XARGS :GUARD T))
  (FORALL (ELEM)
          (NON-EXEC (IMPLIES (IN ELEM SET)
                             (GENERICP ELEM))))
  :REWRITE (IMPLIES (SET-ALL-GENERICP-SK SET)
                    (NON-EXEC (IMPLIES (IN ELEM SET)
                                       (GENERICP ELEM))))
  :SKOLEM-NAME SET-ALL-GENERICP-SK-WITNESS
  :THM-NAME SET-ALL-GENERICP-SK-NECC)

(verify-guards SET-ALL-GENERICP-SK)

(std::defredundant
  :names (genericp
          set-all-genericp
          set-all-genericp-sk-witness
          set-all-genericp-sk
          ))
