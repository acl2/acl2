; This book and comments, modified only as noted below by Matt Kaufmann, were
; produced by Claude and passed along by Eric Smith and Stephen Westfold.  This
; book illustrates a soundness bug fixed before ACL2 Version 8.8.  Note that
; the unmodified book certified with ACL2 built on on Mac arm64 on 11/25/2026,
; before installing "AI fix 6".

; In ACL2 built on Clozure CL for ARM64, `nil` can be proved by reading a stobj bit array at a
; constant index above 32792. This needs no trust tags:

; Logically `(g)` is 1, but compiled code returns 0, because CCL reads a different bit. SBCL is
; not affected. CCL on x86-64 uses a different compiler, which I haven't tested. This file is
; attached as `ccl-sbit-constant-index-nil.lisp`.

; If the bit is written with a constant index too, as in `(update-ari 33000 1 st)` inside `g`,
; then CCL fails to compile `g` with "bad regspec: NIL", and ACL2 rejects the definition. That is
; safe, but it's an unexpected error.

;;; Cause (CCL)

; Both pieces are in CCL's ARM64 compiler, `compiler/ARM64/arm642.lisp`. I reported them as
; [Clozure/ccl#755](https://github.com/Clozure/ccl/issues/755).

; - **Reading:** for a constant index `k` above `arm64::max-1-bit-constant-index` (32792),
;   `arm642-vref1` computes the byte offset of the 32-bit word that holds the bit as
;   `(+ misc-data-offset (ash k -5))`. It should multiply `(ash k -5)` by 4. So compiled
;   `(sbit v k)` reads bit `8*(k>>5) + (k mod 32)`, at any safety level. This also affects `aref`
;   on bit arrays; I tested 1- and 2-dimensional ones.
; - **Writing:** with `(speed 3) (safety 0)` and such a constant index, `arm642-vset` never loads
;   the index into a register, but `arm642-vset1` still passes that register to the
;   index-scaling step, so compilation fails with "bad regspec: NIL".

; ACL2 compiles stobj accessors and updaters this way when `defstobj` is given `:inline t`, and
; also in other guard-verified code that calls `aref` on bit arrays.

(in-package "ACL2")

(defstobj st (ar :type (array bit (40000)) :initially 0) :inline t)

(defun set-bit (i st)
  (declare (xargs :stobjs st :guard (and (natp i) (< i 40000))))
  (update-ari i 1 st))

(defun g ()
  (declare (xargs :guard t))
  (with-local-stobj st
    (mv-let (v st)
      (let ((st (set-bit 33000 st)))
        (mv (ari 33000 st) st))
      v)))

(defthm g-is-1 (equal (g) 1) :hints (("Goal" :in-theory (disable (:e g)))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm g-by-evaluation (equal (g) 0) :hints (("Goal" :in-theory '((:e g)))))
)

; The following was commented out by Matt K. since the event just above now
; fails.
#|
(defthm nil-proved nil :rule-classes nil
  :hints (("Goal" :use (g-is-1 g-by-evaluation) :in-theory nil)))
|#
