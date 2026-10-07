; This book is a variant of integer-length-bad-optimization.lisp, which was
; produced by Claude.  But this time we use an inline wrapper around
; integer-length and check that, even then, we don't see the problematic
; optimization.

(in-package "ACL2")

(defun-inline my-integer-length (n)
  (declare (xargs :guard (natp n)))
  (integer-length n))

(defund foo (n)
  (declare (xargs :guard (natp n)))
  (< (my-integer-length (expt 2 n))
     (expt 2 62)))

(in-theory (disable (:e foo)))

(encapsulate ()
  (local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

  ; Logically NIL whenever n is at least 2^62, since the integer-length is n+1.
  (defthmd foo-when-<=-expt-2-62
    (implies (and (natp n)
                  (<= (expt 2 62) n))
             (not (foo n)))
    :hints (("Goal" :in-theory (enable (:d foo))))))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

; Commented out by Matt Kaufmann: Leads to a raw Lisp error, even when using
; the wrapper (must-fail <form> :expected :hard).

#|
; But (foo (expt 2 62)) evaluates to T via the raw compiled SBCL code.
(defthm contradiction
  nil
  :hints (("Goal" :use ((:instance foo-when-<=-expt-2-62 (n (expt 2 62))))
                  :in-theory (enable (:e foo))))
  :rule-classes nil)
|#

; Matt Kaufmann added the forms below.  For ACL2 built on SBCL before
; 9/12/2026, (foo (expt 2 62)) returned t in raw Lisp, hence so did
; (ignore-errors (foo (expt 2 62))).  After changing ACL2 to address that
; issue, evaluation in raw Lisp of (foo (expt 2 62)) results in an error with
; the message: "Error: can't represent result of left shift".
(defttag :raw)
(progn!
 (set-raw-mode t)
 (assert (equal (ignore-errors (foo (expt 2 62)))
                nil)))
