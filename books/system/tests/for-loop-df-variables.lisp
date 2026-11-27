; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-27: FOR loop$ with OF-TYPE DOUBLE-FLOAT runs raw CL LOOP on rationals declared double-float
; ACL2 Soundness Review, issue S-27.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; Proof of nil, no ttags: certify-book succeeds on SBCL and CCL (ACL2 master 21aaad6).
;
; A FOR loop$ with "of-type double-float" has the guard (DFP y) on its
; iteration variable.  But DFP holds of ordinary rationals that are
; representable as doubles (e.g. 1/2), and those are what a list in ACL2
; contains: the list elements are never raw double-floats.  When the guard of
; K holds (*aokp* non-nil, guards verified), raw Lisp runs the real Common Lisp
;   (LOOP FOR Y OF-TYPE DOUBLE-FLOAT IN X COLLECT (DF< Y (TO-DF 1/1000)))
; with Y bound to the RATIONAL 1/2, compiled at (safety 0) under a
; DOUBLE-FLOAT declaration.  Df primitives such as DF< then operate on the raw
; bits of a non-double, giving garbage (here T instead of NIL; other bodies
; return wrong numbers or crash SBCL with a memory fault).  The *1* code and
; the prover use COLLECT$ on the lambda and compute the logical value NIL.
;
; Nothing reaches the prover from top-level evaluation directly (the prover
; evaluates with *aokp* nil and so takes the COLLECT$ path), but memoize does:
; top-level evaluation of K1 stores the wrong value in K1's memo table, and the
; later ground evaluation of (K1 1/2) during a proof returns it.  This is the
; same memo-table channel used in system/tests/quoted-lambda-return-last-key.lisp.
;
; Related to the nested-DOUBLE-FLOAT fix 7add4ed1d4: that fix ensures that a
; double-float type declaration is atomic, but a FOR loop$ iteration variable
; is not a df (a list cannot hold dfs; see :DOC df, "FOR loop$ expressions"),
; so "of-type double-float" there should be rejected, or the raw LOOP should
; drop the declaration / convert with TO-DF.

(in-package "ACL2")

(defun dfp-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (dfp (car x)) (dfp-listp (cdr x)))
    (null x)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defun k (x)
  (declare (xargs :guard (dfp-listp x)))
  (loop$ for y of-type double-float in x
         collect (df< y (to-df 1/1000))))
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defun k1 (r)
  (declare (xargs :guard (dfp r)))
  (car (k (list r))))

(memoize 'k1)

(value-triple (k1 1/2)) ; raw Lisp LOOP: returns T, which is memoized

(defthm k1-logical
  (equal (k1 1/2) nil)
  :hints (("Goal" :in-theory (disable (:executable-counterpart k1))))
  :rule-classes nil)

(defthm k1-evaluated
  (equal (k1 1/2) t)
  :rule-classes nil)

(defthm contradiction
  nil
  :hints (("Goal" :use (k1-logical k1-evaluated)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#

; Addition by Matt K.: Here is another book suggested by Claude, which
; certified before we prohibited OF-TYPE DOUBLE-FLOAT for FOR-loop$ iteration
; variables.

#|
; H10 (lead F6-6): new path to S-27 that needs no memoize.
; Proof of nil, no ttags, on ACL2 master 21aaad6: (ld "H10-loop-df-clause-processor.lisp")
; proves BAD on SBCL and CCL; certify-book of this file succeeds (SBCL).
;
; S-27 says the prover's own evaluation is correct and only memoize carries the
; raw Common Lisp LOOP value of a FOR loop$ declared OF-TYPE DOUBLE-FLOAT into a
; proof.  But clause processors (and metafunctions) are evaluated with
; attachments allowed (aok = t, eval-clause-processor in prove.lisp), so the raw
; loop$ macro's (cond (*aokp* (loop ...)) ...) takes the CL LOOP branch inside
; the prover itself.  Here (k1 1/2) is NIL logically but T in raw Lisp, so the
; guard-verified clause processor CP returns no subgoals.
; (The other top-level channel, a defconst evaluated by include-book's early load
; of the compiled file, is closed for loop$ by the prohibition on DEFCONST and
; DEFMACRO being ancestrally dependent on loop$/lambda$.)

(in-package "ACL2")

(defun dfp-listp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (dfp (car x)) (dfp-listp (cdr x)))
    (null x)))

(defun k (x)
  (declare (xargs :guard (dfp-listp x)))
  (loop$ for y of-type double-float in x
         collect (df< y (to-df 1/1000))))

(defun k1 (r)
  (declare (xargs :guard (dfp r)))
  (car (k (list r))))

(defevaluator evl evl-list ((if x y z)))

(defun cp (cl)
  (declare (xargs :guard t))
  (if (equal (k1 1/2) nil) ; logically true; T in raw Lisp
      (list cl)
    nil))

(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a)
                (evl (conjoin-clauses (cp cl)) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(defthm bad nil
  :hints (("Goal" :clause-processor (cp clause)))
  :rule-classes nil)
(value-triple (cw "~%NIL-PROVED~%"))
|#
