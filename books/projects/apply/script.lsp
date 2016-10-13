; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; [Note to Moore: To run this, use:
; % applycert
; which will copy the relevant files to temp-books/ and certify them,
; and save temp-books/* to saved-snapshots/<date>

; See /u/bin/applycert
; ]

; Script for Certifying the Apply Family Books

; Note: All include-book relations between the books in the /projects/apply/
; directory are made explicit here by doing every relevant include-book before
; invoking certify-book.  That is, no book on this directory contains an
; include-book event of any book on this directory.  The only include-book
; events found within the books on this directory are to the following commonly
; used community books:

; (include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
; (include-book "tools/flag" :dir :system)
; (include-book "misc/eval" :dir :system)

; So by studying this file you can see the interdependencies of the apply
; books.

; ground zero
(certify-book "apply-prim")
(ubt! 1)

; ground zero
(include-book "apply-prim")
(certify-book "constraints" 1)
(ubt! 1)

; ground zero
(include-book "constraints")
(certify-book "apply" 1)
(ubt! 1)

; ground zero
(include-book "apply")
(certify-book "user-book" 1)
(ubt! 1)

; ground zero
(include-book "apply")
(certify-book "foldr-exercises" 1)
(ubt! 1)

; ground zero
(include-book "apply-prim")
(certify-book "doppelgangers" 1)
(ubt! 1)

; ground zero
(include-book "user-book")
(include-book "doppelgangers")
(defattach badge-userfn badge-userfn!)
(defattach apply$-userfn apply$-userfn!)
(certify-book "defattach-demo" 4)  ; a few illustrative evaluations
(ubt! 1)

; The above script is sort of a simulation of our basic idea: The doppelgangers
; built from user-book.lisp can be attached to the two apply$ stubs producing
; an evaluation theory in which we can execute mapping functions as expected.

; That evaluation theory is technically obtained by adding the two attachment
; equations as axioms, which is sound since we know the attachments satisfy the
; constraints of the stubs.  (Note that we do not bother to attach anything to
; untame-apply$ and untame-apply$ because we are happy for them to be
; unevaluable (i.e., signal some sort of error) even in the evaluation theory.)

; But below we are interested in proving that all the warrants are valid in the
; evaluation theory that results from the two attachments above.  ACL2 doesn't
; support proofs in the evaluation theory, it just supports evaluations in the
; evaluation theory.  To prove things in an evaluation theory we have to create
; a current theory that is the evaluation theory we want.  We do that by
; rebuilding apply.lisp and user-book.lisp on top of the two attachment
; equations noted above.  These books are called evaluation-apply.lisp and
; evaluation-user-book.lisp and are just copies of apply.lisp and
; user-book.lisp (as made with copy-file below) but certified with different
; portcullises.  The definitional equations of evaluation-user-book.lisp are
; the evaluation theory we want.

; When we finish building evaluation-apply.lisp and evaluation-user-book we
; will prove a bunch of lemmas, in evaluation-lemmas.lisp, so that we can
; verify the validity of the warrants.

; So here we go:

; As is evident above, user-book.lisp was certified on top of (i.e., with
; portcullis) apply.lisp, which was certified on top of constraints.lisp.
; Constraints.lisp constrained the four apply$ stubs (only two of which concern
; us).  Our plan requires rebuilding this stack starting from defuns for the
; two critical apply$ stubs, said defuns being the attachment equations
; justified above.  So we copy apply.lisp and user-book.lisp with the intention
; of (re)-certifying them with the defined portcullises.

; ground zero
(certify-book "copy-file")
(copy-file "apply.lisp" "evaluation-apply.lisp" state)
(copy-file "user-book.lisp" "evaluation-user-book.lisp" state)
(ubt! 1)

; Note that the copies are named evaluation-apply.lisp and
; evaluation-user-book.lisp.

; Now we certify evaluation-apply.lisp (aka apply.lisp) with a portcullis
; consisting of the two attachment equations from the defattach events above.
; We actually just defun the previously constrained functions to be their
; doppelgangers.

; ground zero
(include-book "doppelgangers")
(defun badge-userfn (fn)
  (declare (xargs :guard t))
  (badge-userfn! fn))
(defun apply$-userfn (fn args)
  (declare (xargs :guard (true-listp args)))
  (apply$-userfn! fn args))
(certify-book "evaluation-apply" 3)
(ubt! 1)

; Next, we certify evaluation-user-book.lisp with the portcullis
; evaluation-apply.lisp.  This gives us the evaluation theory corresponding to
; user-book.lisp.

; ground zero
(include-book "evaluation-apply")
(certify-book "evaluation-user-book" 1)
(ubt! 1)

; Note: Technically this is overkill and, in general, could hurt us in the next
; step.  By certifying all of evaluation-user-book.lisp (aka user-book.lisp) in
; this portcullis we produce the desired evaluation theory definitions but we
; also load up the theory with a lot of ACL2 rules from user-book.lisp.  These
; random rules might actually get in our way in proving the evaluation lemmas
; we'll need and in proving the validity of the warrants.  For example, a rule
; in the user-book might rewrite collect to foldr and make some lemma we need
; about collect versus collect! harder to prove.  In a sense, we wish we could
; just certify a book with the definitions from user-book.lisp in it.  And, of
; course, we could do that but it complicates the process.  Theoretically, it
; doesn't matter: when regarded as merely a theory rather than a set of rules,
; this is right and we're keeping it simple because, fortunately, none of the
; rules in user-book actually hurt us (by a little design and some luck).  But
; if we someday tried to actually implement the process to produce the
; evaluation theory and prove the warrants, we'd want to be more careful!

; Next, we derive a few useful lemmas.  It is always ok to prove lemmas in a
; theory: they're already in there and all we're doing is pointing out a few
; useful ones for ACL2.

(include-book "evaluation-user-book")
(certify-book "evaluation-lemmas" 1)
(ubt! 1)

; And now we show that all warrants in user-book.lisp are valid in the
; evaluation theory.

; ground zero
(include-book "evaluation-lemmas")
(certify-book "all-warrants-valid" 1)
(ubt! 1)

; TODO: To be truly satisfied that we've done what we said we'd do, we ought to
; confirm that all-warrants-valid.lisp contains every warrant, i.e., a theorem
; of the form (APPLY$-WARRANT-fn), for every fn in the badge-table's
; :badge-userfn-structure such that the associated badge has :authorization-flg
; t.  We could, perhaps write a make-event that does that.  Instead, we just
; created all-warrants-valid by hand, adding an appropriate defthm for each
; such fn every time we added a new warranted fn to user-book.lisp and
; doppelgangers.lisp.
