; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.

; ============================================================================
; PROOF OF NIL: defun redundancy ignores :WELL-FOUNDED-RELATION
; ============================================================================
; ACL2 recognizes a proposed defun as "redundant" with an existing one by
; comparing (in non-identical-defp, defuns.lisp) their formals, body, guards,
; types, stobjs, :ruler-extenders and :measure subset -- but NOT their
; :well-founded-relation.  Past proofs of nil of exactly this shape were closed
; by adding the :ruler-extenders check (note-3-6) and the :measure check
; (note-3-0-2); the :well-founded-relation dimension was never added.
;
; Here the LOCAL f is admitted with the real relation O< and terminates.  The
; non-local f, identical except for :well-founded-relation NEVER<, is declared
; redundant -- so its (false) measure conjecture, (NEVER< (acl2-count (cdr x))
; (acl2-count x)) = NIL, is never checked.  NEVER< is (vacuously) a legitimate
; well-founded relation, so the rule below is admissible; but no recursion can
; actually be justified by it.  After the book is included, f's stored
; justification uses NEVER<, yielding a bogus :termination-theorem.
(in-package "ACL2")

(defun never< (x y) (declare (ignore x y)) nil)
(defun id (x) x)

(defthm never<-is-well-founded
  (and (implies (natp x) (o-p (id x)))
       (implies (and (natp x) (natp y) (never< x y))
                (o< (id x) (id y))))
  :rule-classes :well-founded-relation)

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(encapsulate ()
  (local (defun f (x)
           (declare (xargs :measure (acl2-count x)))
           (if (consp x) (f (cdr x)) x)))
  ;; Identical to the above except for the (false) well-founded relation.
  ;; Accepted as redundant; its measure conjecture is never proved.
; The must-fail wrapper below was added by Matt Kaufmann, as the following
; definition of f is no longer redundant as of mid-September, 2026.
  (must-fail
  (defun f (x)
    (declare (xargs :measure (acl2-count x)
                    :well-founded-relation never<))
    (if (consp x) (f (cdr x)) x))
  ))

; Commented out by Matt Kaufmann:
#|
;; f's bogus termination-theorem: nothing decreases under NEVER<, so f "proves"
;; that it never recurs, i.e. no argument is a cons.
(defthm no-conses
  (not (consp x))
  :rule-classes nil
  :hints (("Goal" :use (:termination-theorem f))))

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance no-conses (x '(1))))))
|#
