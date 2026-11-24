; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-233 (lead F1-187, stage-2 batch G85): a direct call of the touchable verify-guards-fn1 marks a LAMBDA guard-verified
; without checking its callees (a :GOOD cl-cache line that is never invalidated); raw aset1 then writes out of bounds
; (the S-42 layout, index for sbcl).  Proves nil and certifies, no trust tags, on sbcl at 21aaad6 and 947ff84343.
; Control: without the make-event, the top-level apply$ is refused.
;
; G85 (lead F1-187.A): proof of NIL, certifiable, no trust tags.  (sbcl layout:
; index 10; see the -ccl variant for CCL.)
;
; VERIFY-GUARDS-FN1 (defuns.lisp) is a touchable :program function (it is on
; *initial-program-fns-with-raw-code*, not on the untouchables).  Called
; directly, it proves the guard obligations of NAMES but skips everything
; CHK-ACCEPTABLE-VERIFY-GUARDS checks, in particular that the functions called
; are guard-verified, and it adds :GOOD cl-cache lines
; (add-good-lambda-objects-to-cl-cache) for the LAMBDAs it is given, stamped
; with the number of the next event.  No world is installed, so nothing ever
; invalidates the lines.  Below, H is a :logic function whose guards are NOT
; verified (its ASET1 call has false obligations); the LAMBDA calling H has
; trivial obligations (H's guard is T), so the direct call makes it :GOOD.
; Top-level APPLY$ then runs the LAMBDA's compiled code, i.e. raw H, i.e. raw
; ASET1 without a bounds check: writing at index 10 of array A changes array B
; (the S-42 layout), contradicting LEMMA, which the prover re-evaluates.
; Tried: (ld ...) and (certify-book ...) on SBCL at master 947ff84343,
; 15e42ee881 and 21aaad6 (acl2-sbcl); control without the make-event: the
; apply$ call errors (H has no badge) and BAD fails.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defconst *ab*
  (list (compress1 'a '((:header :dimensions (4) :maximum-length 6
                                 :default 0 :name a)
                        (0 . 0) (1 . 0) (2 . 0) (3 . 0)))
        (compress1 'b '((:header :dimensions (4) :maximum-length 6
                                 :default 9 :name b)
                        (0 . 9) (1 . 9) (2 . 9) (3 . 9)))))
(defconst *a* (car *ab*))
(defconst *b* (cadr *ab*))
(defthm lemma
  (equal (aref1 'b *b* 0) 9)
  :rule-classes nil)

; Guard T, guards not verified (they would need (array1p 'a a), bounds, ...).
(defun h (a i)
  (declare (xargs :verify-guards nil))
  (aset1 'a a i 'boom))

(defconst *L* '(lambda (a i) (h a i)))

; Direct call: the LAMBDA's own obligations are trivial (H's guard is T).
(must-fail
(make-event
 ; The call below fails: untouchable function
 (er-progn (verify-guards-fn1 (list *L*) nil nil nil t 'top state)
           (value '(value-triple :done))))
)

; The following are commented out since the event just above now fails.
#|
; Top-level apply$ runs the compiled LAMBDA: raw H, raw ASET1 at index 10.
(value-triple (apply$ *L* (list *a* 10)))

(defthm nil-proved
  nil
  :hints (("Goal" :use lemma))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
