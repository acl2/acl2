; Kestrel's Contributions to the ACL2 System Code
;
; Copyright (C) 2016
;   Kestrel Institute (http://www.kestrel.edu)
;   Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains Kestrel's contributions to the ACL2 system code.
; In particular, it contains forms
; to put some system code into logic mode,
; guard-verify it,
; and prove theorems about it.
; These contributions may be eventually incorporated into the ACL2 system code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination def-body)

; Guard verification for def-body is currently impossible because we need to
; know that (getpropc fn 'def-bodies nil wrld) satisfies listp (even though we
; "know" that it even satisfies true-listp).  A solution could be to add that
; guard; another could be to check listp at runtime.  The latter adds a small
; but unfortunate bit of inefficiency.  Adding a guard might be OK, but perhaps
; safe-mode could then make the function slow.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination latest-body)

(verify-guards latest-body)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination body)

; Guard verification would require def-body to be guard-verified (see comment
; above).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination logical-namep)

; For verify-guards, needs to add this guard for logical-namep:

; (declare (xargs :guard (and (symbolp name) (plist-worldp wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination stobjs-out)

; Consider replacing stobjs-out with the following definition, to support guard
; verification.

#||
(defun stobjs-out (fn w)

; Warning: keep this in sync with get-stobjs-out-for-declare-form.

; See the Essay on STOBJS-IN and STOBJS-OUT.

; Note that even though the guard implies (not (member-eq fn
; *stobjs-out-invalid*)), we keep the member-eq test in the code in case
; stobjs-out is called from a :program-mode function, since in that case the
; guard may not hold.

  (declare (xargs :guard (and (symbolp fn)
                              (plist-worldp w)
                              (not (member-eq fn *stobjs-out-invalid*)))))
  (cond ((eq fn 'cons)
; We call this function on cons so often we optimize it.
         '(nil))
        ((member-eq fn *stobjs-out-invalid*)
         (er hard! 'stobjs-out
             "Implementation error: Attempted to find stobjs-out for ~x0."
             fn))
        (t (getpropc fn 'stobjs-out '(nil) w))))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination macro-args)

; For verify-guards, need to add this guard to macro-args:

; (declare (xargs :guard (and (symbolp x) (plist-worldp w))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination signature-fns)

; For verify-guards, need to add a suitable guard to signature-fns.  The
; comment in signature-fns starts with "Assuming that signatures has been
; approved by chk-signatures"; unfortunately, chk-signatures modifies state.  A
; solution could be to defined chk-signatures in terms of a suitable
; chk-signatures-cmp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination access-event-tuple-namex)

; Guard verification would require a suitable guard.  We know that the input is
; an event-tuple, but there seems to be no predicate such as event-tuple-p.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination termify-clause-set)

; Consider replacing termify-clause-set with the following definition, to
; support guard verification.  Then the following two events suceed in place of
; the one just above:
; (verify-termination termify-clause-set (declare (xargs :verify-guards nil)))
; (verify-guards termify-clause-set)

#||
(defun termify-clause-set (clauses)

; This function is similar to termify-clause except that it converts a
; set of clauses into an equivalent term.  The set of clauses is
; understood to be implicitly conjoined and we therefore produce a
; conjunction expressed as (if cl1 cl2 nil).

  (declare (xargs :guard (pseudo-term-list-listp clauses)))
  (cond ((null clauses) *t*)
        ((null (cdr clauses)) (disjoin (car clauses)))
        (t (mcons-term* 'if
                        (disjoin (car clauses))
                        (termify-clause-set (cdr clauses))
                        *nil*))))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination formalized-varlistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination throw-nonexec-error-p1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination throw-nonexec-error-p)
