; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a bug fixed before
; ACL2 Version 8.8.

(in-package "ACL2") ; added by Matt K. to make this a certifiable book

; E3-c: invalidation SEMANTICS check (needs a trust tag only to shrink the ring
; to 3 so the full-ring case is cheap to reach).  Three :GOOD lines must all
; become :UNKNOWN after the retraction -- including the one in the ring's last
; slot, which is what would be missed by an off-by-one in the new size bound.
; EXPECT-AFTER-FIX: ":status :GOOD" x3 before, ":status :UNKNOWN" x3 after.
; On stock ACL2 this file hangs at the (ubt! 'f).
(include-book "projects/apply/top" :dir :system)
; (set-inhibit-output-lst '(proof-tree prove event summary)) ; commented out by Matt K.: not an event
(defttag :cl)
(progn! (set-raw-mode t) (cl-cache-init 3))
(defun$ f (x) (declare (xargs :guard t)) (cons x x))
(value-triple (apply$ '(lambda (x) (f x)) (list 1)))
(value-triple (apply$ '(lambda (x) (cons x x)) (list 2)))
(value-triple (apply$ '(lambda (x) (cons x (cons x 'nil))) (list 3)))
; (cw "MARK before-retraction~%") ; commented out by Matt K.: not an event
; (print-cl-cache) ; commented out by Matt K.: not an event
(make-event (er-progn ; wrapper to (ubt! 'f) added by Matt K.
             (ubt! 'f)
             (value '(value-triple nil))))
; (cw "MARK after-retraction~%") ; commented out by Matt K.: not an event
; (print-cl-cache) ; commented out by Matt K.: not an event
; (cw "MARK ALL-DONE~%") ; commented out by Matt K.: not an event
