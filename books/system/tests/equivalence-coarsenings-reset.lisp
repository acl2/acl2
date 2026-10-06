; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a bug fixed before ACL2 Version 8.8.
; The fix was to ignore a second :equivalence rule for the same equivalence
; relation.

; N195: add-equivalence-rule overwrites 'coarsenings instead of extending it, and
; chk-acceptable-equivalence-rule's "already known to be an equivalence relation"
; guard is discarded under include-book.  So including eqv2/b -- which only
; re-states that R is an equivalence relation, under a different theorem name,
; and never mentions S -- destroys eqv2/a's proved (DEFREFINEMENT R S).
;
; The ASSERT-EVENT below states the CORRECT behaviour: R is still a refinement of
; S after both books are included.  It FAILS while the defect is present and
; SUCCEEDS once add-equivalence-rule either no-ops on an already-known
; equivalence relation (as add-refinement-rule does) or extends and re-closes
; rather than replacing.
(in-package "ACL2")
(include-book "eqv2/a")
(include-book "eqv2/b")
(assert-event (and (refinementp 'r 's (w state)) t))
