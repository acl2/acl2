; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.

; a1.lisp -- certified proof of NIL from the boole$ logic/raw drift.
;
; axioms.lisp:17168 carries the sync note
;   "Warning: Keep the following defconst forms in sync with *boole-array*."
; covering the *BOOLE-n* defconsts, and acl2.lisp:2944 carries its twin
;   "Keep this in sync with the defconst forms just above the definition of
;    boole$."
; on *boole-array*.  The index<->constant mapping is in fact in sync.  What
; drifted is the third copy: the #+acl2-loop-only (logical) body of boole$,
; which spells out the RESULT of each op.
;
;   #-acl2-loop-only  (boole (aref *boole-array* op) i1 i2)
;   #+acl2-loop-only  (cond ... ((eql op *BOOLE-SET*) 1) ...)
;
; *BOOLE-SET* is index 14, and (aref *boole-array* 14) is Common Lisp's
; BOOLE-SET, for which the standard specifies "all one bits", i.e. the
; integer -1 -- not 1.  :DOC boole$ agrees with raw Lisp ("*boole-set* the
; constant -1 (all one bits)"); only the logical body says 1.
;
; So the axiom introduced by the defun and the executable counterpart derived
; from raw Lisp disagree on a ground term, and NIL follows.
;
; No ttag, no skip-proofs, no defaxiom, no include-book.

(in-package "ACL2")

; (1) What the AXIOM (the #+acl2-loop-only body) says.  Proved in the minimal
;     theory augmented only with the definition rule for boole$, so that the
;     executable counterpart of boole$ cannot participate.

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm boole-set-is-1-by-definition
  (equal (boole$ *boole-set* 5 7) 1)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '((:definition boole$))
                                             (theory 'minimal-theory)))))
)

; Added by Matt K. to show the fix:
(defthm boole-set-is-minus-1-by-definition
  (equal (boole$ *boole-set* 5 7) -1)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '((:definition boole$))
                                             (theory 'minimal-theory)))))

; (2) What RAW LISP says, via the executable counterpart of boole$.

(defthm boole-set-is-minus-1-by-evaluation
  (equal (boole$ *boole-set* 5 7) -1)
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '((:executable-counterpart boole$))
                                             (theory 'minimal-theory)))))

;; Commented out by Matt Kaufmann (as the rest of the file is irrelevant after
; the bug fix):

#|
; (3) 1 /= -1.

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal"
           :use (boole-set-is-1-by-definition
                 boole-set-is-minus-1-by-evaluation))))
|#
