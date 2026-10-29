; Known-answer checks for rev_range.rs -- reversed-range iteration
; (`for i in (a..b).rev()`), the upstream memshift32 shape.  Rev<Range>'s
; `next` and `Iterator::rev` are the real translated core bodies; only
; `Range::next_back` and the blanket `into_iter` are backend-synthesized.
(in-package "ACL2")
(include-book "rev_range")

(assert-event (equal (rev-range-sum-rev 100 (list 1 2 3 4 5 6 7 8)) (ok 36)))

(assert-event
 (equal (rev-range-shift-up 100
          (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24)
          0)
        (ok (list 1 2 3 4 5 6 7 8 1 2 3 4 5 6 7 8 17 18 19 20 21 22 23 24))))

(assert-event
 (equal (rev-range-shift-up 100
          (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24)
          8)
        (ok (list 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 9 10 11 12 13 14 15 16))))
