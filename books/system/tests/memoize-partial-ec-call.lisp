; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-56: memoize-partial: an ec-call recursive call escapes the flet and runs with limit 0
; ACL2 Soundness Review, issue S-56.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags; certifies.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; H2 candidate (soundness), found under lead F8-1977 (memoize :total).
; memoize-partial executes F by the body of F-LIMIT with LIMIT bound to 0 and
; with recursive calls of F-LIMIT redirected to F by an FLET
; (memoize-partial-def, other-events.lisp).  The table guard checks that LIMIT
; occurs only as the last argument of recursive calls
; (free-exactly-in-last-arg-of-calls), and accepts a call wrapped in EC-CALL.
; But EC-CALL calls *1*F-LIMIT, which the FLET does not redirect, so that call
; runs with limit 0 and returns the base value.  Here both calls in
; (equal (f-limit 0 limit) (ec-call (f-limit 0 limit))) are logically the same
; term, so F-LIMIT and hence F are 'C at n = 1 for every limit; but raw F
; compares (f 0) = Z with *1*F-LIMIT(0,0) = C and returns 'D.
; Proves NIL at the top level and certifies as a book (cert.pl, no ttag).
; Verified on master 21aaad6, SBCL and CCL.
(in-package "ACL2")
(defun f-limit (n limit)
  (declare (xargs :guard (and (natp n) (natp limit)) :measure (nfix limit)))
  (if (zp limit)
      'c
    (let ((limit (1- limit)))
      (if (zp n)
          'z
        (if (equal (f-limit 0 limit) (ec-call (f-limit 0 limit)))
            'c
          'd)))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(memoize-partial f)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm f-limit-1 (equal (f-limit 1 l) 'c))
(defthm f-1-logic (equal (f 1) 'c)
  :hints (("Goal" :in-theory (disable (:e f))))
  :rule-classes nil)
(defthm f-1-exec (equal (f 1) 'd) :rule-classes nil) ; by evaluation
(defthm bad nil :hints (("Goal" :use (f-1-logic f-1-exec))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
