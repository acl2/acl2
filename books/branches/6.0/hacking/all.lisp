(in-package "ACL2")

; Modification by Matt K. after v4-3: Removed :load-compiled-file :comp, which
; was part of all include-book forms just below, in support of provisional
; certification.  Presumably the indicate books have already been compiled by
; now, anyhow.

(include-book "hacker")

(include-book "defstruct-parsing")
(include-book "rewrite-code")

(include-book "defcode"
              :ttags ((defcode)))
(include-book "raw")
(include-book "redefun")
(include-book "bridge")
(include-book "subsumption")
(include-book "table-guard"
              :ttags ((defcode) (table-guard)))
