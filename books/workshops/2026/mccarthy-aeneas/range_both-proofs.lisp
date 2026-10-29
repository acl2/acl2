; Known-answer checks for range_both.rs -- the naming-collision regression
; crate (Range<usize> and Range<i32> instantiated together).  Certifying
; this book proves both monomorphized iterator instances extract, admit,
; and execute.
(in-package "ACL2")
(include-book "range_both")

(assert-event (equal (range-both-sum-usize 100 (list 1 2 3 4)) (ok 10)))
(assert-event (equal (range-both-count-i32 100) (ok 10)))
