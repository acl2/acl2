; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

; This book is based on an example produced by Claude and passed along by Eric
; Smith.  It illustrates a soundness bug fixed before ACL2 Version 8.8.  The
; bug was in the rewriter's handling of IMPLIES (function rewrite in
; rewrite.lisp).  When the conclusion of (implies test concl) rewrote to nil,
; the rewriter returned (dumb-negate-lit rewritten-test), which for a test
; (not p) is p.  That is only iff-equivalent to the Boolean (not (not p)), yet
; it was returned even where the result had to be equal to the original term.
; Now that shortcut is taken only where iff-equivalence suffices, or where the
; result is known by type reasoning to be Boolean.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; Keep (not p) from being expanded, so that the rewriter sees a NOT call.
(in-theory (disable not))

; Previously provable, although false: (implies (not 3) nil) is t, not 3.  The
; :do-not hint keeps the IMPLIES term intact until the rewriter sees it.
(must-fail
 (defthm implies-not-p-nil-is-p
   (equal (implies (not p) nil) p)
   :hints (("Goal" :do-not '(preprocess)))
   :rule-classes nil))

(must-fail
 (defthm contradiction
   nil
   :hints (("Goal" :use (:instance implies-not-p-nil-is-p (p 3))))
   :rule-classes nil))

; In an iff context the shortcut is still sound, and is still taken.
(defthm implies-not-p-nil-iff-p
  (iff (implies (not p) nil) p)
  :hints (("Goal" :do-not '(preprocess)))
  :rule-classes nil)

; The shortcut is also still taken when the result is known to be Boolean, here
; by the type-prescription rule for F.  (Example from Matt Kaufmann.)
(defun f (x)
  (consp x))

(in-theory (disable f))

(defthm implies-not-f-nil-is-f
  (equal (implies (not (f x)) nil) (f x))
  :hints (("Goal" :do-not '(preprocess)))
  :rule-classes nil)
