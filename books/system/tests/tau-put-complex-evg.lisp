; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; N167: tau-put (tau.lisp, the Tau-Put Table, entries 25/26/29/30) decides its
; table entry with Common Lisp < applied to (fix a), where a is the evg of an
; (EQUAL x 'a) tau recognizer.  FIX is the IDENTITY on a complex rational and
; CL's < requires REAL, so an ordinary defthm reaches Q.E.D. and then aborts
; from raw Lisp while the event is being installed.
;
; NOTE THE DIRECTION: unlike the must-fail books in this suite, these are plain
; defthms.  The book fails to certify while the defect is present and certifies
; once it is fixed -- the same "certifies exactly when the bug is absent"
; convention, reached the other way round, because the defect is a crash rather
; than an exploit.
;
; tau's own complex-aware comparators <?-number-v-rational /
; <?-rational-v-number are what these four lines need; eval-tau-interval1 and
; collect-<?-x-k already use them.
(in-package "ACL2")

; --- CONTROLS: the same four shapes with constants FIX handles correctly.
; These must always be admitted; if one of them fails, the harness is broken
; rather than the defect being present.
(defthm tau-ctl-rational  (implies (equal x 5)     (< x 9)))
(defthm tau-ctl-symbol    (implies (equal x 'abc)  (< x 9)))
(defthm tau-ctl-string    (implies (equal x "s")   (< x 9)))
(defthm tau-ctl-cons      (implies (equal x '(1))  (< x 9)))
(defthm tau-ctl-char      (implies (equal x #\a)   (< x 9)))

; --- The four defective table entries.  Each is a theorem of ACL2, since < is
; the lexicographic completion and is total.
(defthm tau-put-entry-25 (implies (equal x #c(1 1)) (< x 3)))
(defthm tau-put-entry-26 (implies (equal x #c(1 1)) (not (< x 1))))
(defthm tau-put-entry-29 (implies (equal x #c(1 1)) (< 0 x)))
(defthm tau-put-entry-30 (implies (equal x #c(1 1)) (not (< 2 x))))
