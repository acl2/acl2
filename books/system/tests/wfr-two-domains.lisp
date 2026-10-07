; This book, modified by Matt Kaufmann only as noted below, was produced by
; Claude and passed along by Eric Smith.  It illustrates a bug in ACL2 Version
; 8.7 fixed before ACL2 Version 8.8.  It might well have been a soundness bug,
; though that is not demonstrated here.

; N196: chk-acceptable-well-founded-relation-rule forbids a second domain for a
; relation already in 'well-founded-relation-alist, but that check is discarded
; under include-book and add-well-founded-relation-rule conses onto the FRONT of
; the alist with no check.  Consumers use assoc-eq, so the last book included
; decides the effective domain.
;
; The ASSERT-EVENT states the CORRECT behaviour: MYREL's effective domain is
; still DOM1, the one established by wfr/wa.  It FAILS while the defect is
; present (the answer is DOM2).  If the eventual fix instead makes the second
; installation a hard error, this book will fail to certify rather than turning
; green -- the suite's failure classifier will say so, and that is still a
; change from the recorded state.
(in-package "ACL2")
(include-book "wfr/wa")
; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)
; Added by Matt Kaufmann: I added the following must-fail wrapper.  The check
; on well-founded-relation rules is no longer skipped during include-book, so
; this second include-book now causes an error saying that "We do not permit
; more than one domain to be associated with a well-founded relation."
(must-fail (include-book "wfr/wb"))
(assert-event
 (eq (cadr (assoc-eq 'myrel (global-val 'well-founded-relation-alist (w state))))
     'dom1))
