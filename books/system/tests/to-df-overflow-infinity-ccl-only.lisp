; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-30: CCL: to-df of an integer just below 2^1024 returns +infinity without an overflow trap
; ACL2 Soundness Review, issue S-30.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with CCL 1.13 only (SBCL signals floating-point overflow); no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; Proof of nil in CCL 1.13 (no ttags): certify-book succeeds on ACL2 master
; 21aaad6 built on CCL (x86-64 Linux).  On SBCL the book fails, as it should,
; with a FLOATING-POINT-OVERFLOW error.
;
; ACL2 relies on floating-point traps (break-on-overflow-and-nan sets CCL's
; FPU mode to trap overflow; df-signal? and check-fp-signals rely on it), so
; that a df operation never returns an infinity or NaN: such a value has no
; rational meaning in the logic.  But CCL's (float n 0d0), which is raw TO-DF,
; does not signal overflow for an INTEGER n in [2^1024 - 2^970, 2^1024): it
; returns +infinity (printed 1E++0), and (rational +infinity) is 2^1024 in CCL.
; (Some ratios just below 2^1024 also give +infinity on CCL: see S-30-ratio-overflow-infinity-ccl-only.lisp.  SBCL traps in all these cases.)
;
; So (from-df (to-df (r-big))) evaluates to 2^1024, and (df/ 1 (to-df (r-big)))
; evaluates to 0 (1/inf).  In the logic, that quotient is
; (df-round (/ 1 2^1024)) = (df-round 2^-1024), and 2^-1024 is a (subnormal)
; double, so df-round-is-identity-for-dfp makes it 2^-1024, not 0.
;
; Related to (but different from) S-15: here the host Lisp produces a non-finite
; double without signalling, rather than misrounding a finite value.
; The commit 3880619ce7 changed df-signal? for CCL on arm64 only; on x86-64,
; CCL df operations rely on FPU traps, which this integer conversion bypasses.
; Fix idea: in raw TO-DF (and anywhere ACL2 converts with FLOAT), check the
; result (e.g. compare its magnitude with most-positive-double-float, or use
; df-signal? style checks) for CCL, or reject integers >= 2^1024 - 2^970 before
; converting; and report the missing trap to the CCL maintainers.

(in-package "ACL2")

(defun r-big ()
  (declare (xargs :guard t))
  (- (expt 2 1024) (expt 2 970))) ; halfway between max double and 2^1024

(defun big-df ()
  (declare (xargs :guard t))
  (from-df (to-df (r-big))))

(defttag t)

; Matt K. addition, to show that a raw Lisp error now occurs:
(progn!
 (set-raw-mode t)
 (assert (equal (ignore-errors (big-df)) nil)))

; The following were commented out by Matt K. since the first event below
; causes a raw Lisp error.
#|
(defun recip ()
  (declare (xargs :guard t))
  (from-df (df/ (to-df 1) (to-df (r-big)))))

(defthm recip-val ; by evaluation in CCL: 1/+inf = 0
  (equal (recip) 0)
  :rule-classes nil)

(defthm big-df-val ; by evaluation in CCL: (rational +inf) = 2^1024
  (equal (big-df) (expt 2 1024))
  :rule-classes nil)

(defthm recip-is ; by the definitions
  (equal (recip) (df-round (/ 1 (big-df))))
  :hints (("Goal" :in-theory (e/d (big-df recip binary-df/ from-df)
                                  ((:e recip) (:e big-df) (:e r-big)
                                   (:e to-df) (:e binary-df/)))))
  :rule-classes nil)

(defthm small-dfp ; 2^-1024 is a subnormal double
  (dfp (expt 2 -1024))
  :rule-classes nil)

(defthm contradiction
  nil
  :hints (("Goal"
           :use (recip-val recip-is big-df-val small-dfp
                           (:instance df-round-is-identity-for-dfp
                                      (r (expt 2 -1024))))
           :in-theory (union-theories '((:e expt) (:e binary-*) (:e unary-/)
                                        (:e equal))
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
