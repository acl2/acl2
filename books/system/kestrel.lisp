; Kestrel's Contributions to the ACL2 System Code
;
; Copyright (C) 2016-2022
;   Kestrel Institute (http://www.kestrel.edu)
;   Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Alessandro Coglio (coglio@kestrel.edu)
;   Eric Smith (eric.smith@kestrel.edu)
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains Kestrel's contributions to the ACL2 system code.
; In particular, it contains forms
; to put some system code into logic mode and possibly guard-verify it.
; These contributions may be eventually incorporated into the ACL2 system code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; The following is for strip-cadrs, used in access-event-tuple-namex.
(include-book "verified-termination-and-guards")

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

; Guard verification would require a guard specifying something about the
; layout of the known-package-alist.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination stobjs-out) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination macro-args) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination signature-fns)

; For verify-guards, need to add a suitable guard to signature-fns.  The
; comment in signature-fns starts with "Assuming that signatures has been
; approved by chk-signatures"; unfortunately, chk-signatures modifies state.  A
; solution could be to define chk-signatures in terms of a suitable
; chk-signatures-cmp.  But then several subfunctions would need -cmp versions;
; is it worth the effort?

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination access-event-tuple-namex)

; Guard verification would require not only guard verification for
; signature-fns, but also a suitable guard for access-event-tuple-namex.  We
; know that the input is an event-tuple, but there seems to be no predicate
; such as event-tuple-p.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination termify-clause-set (declare (xargs :verify-guards nil)))

(verify-guards termify-clause-set)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination formalized-varlistp) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination throw-nonexec-error-p1) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination throw-nonexec-error-p) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination stobjp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination compute-stobj-flags)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination defun-mode) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination doublet-listp) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination implicate) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination add-suffix-to-fn) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "subcor-var") ; for subcor-var1

(verify-termination fsubcor-var) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination get-brr-local)

(verify-termination ens-maybe-brr)

; The above two forms ensure that the expansion of the disabledp macro is in
; logic mode.

; For verify-guards, we need to add a suitable guard to lookup-brr-stack, and
; perhaps to the other three functions above as well.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination the-live-var) ; and guards

(verify-termination logical-name-type) ; and guards

(verify-termination new-namep) ; and guards

(verify-termination chk-all-but-new-name-cmp) ; and guards

(verify-termination attach-stobj-guard-msg) ; and guards

(verify-termination attach-stobj-guard) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-termination partition-rest-and-keyword-args1) ; and guards

(verify-termination partition-rest-and-keyword-args2) ; and guards

(verify-termination partition-rest-and-keyword-args) ; and guards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local (include-book "kestrel/acl2-arrays/aset1" :dir :system))
  (local (include-book "kestrel/acl2-arrays/dimensions" :dir :system))
  (local (include-book "kestrel/acl2-arrays/compress1" :dir :system))

  (local (in-theory (disable array1p)))

  (verify-termination aset1-lst) ; and guards
  )
