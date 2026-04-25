; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book runs (add-guards-as-assertions-all), which checks top-level calls
; of built-in functions that are in :logic mode, guard-verified.  But first, a
; more limited check, (add-guards-as-assertions-svga), checks just those
; functions that are guard-verified outside the system, i.e., are in
; *system-verify-guards-alist*.  After that, the full is done on
; (mini-proveall) and several books, which have been chosen arbitrarily.  It
; should be fine to replace or add to those books.

; The use of encapsulate below is to undo the effect of the local event
; within.

; (depends-on "check-system-guards-raw.lsp")

(in-package "ACL2")

(local (include-book "tools/include-raw" :dir :system))

(defttag :check-system-guards)

(local (include-raw "check-system-guards-raw.lsp"))

(deflabel init)

(local (progn!
        (set-raw-mode t)
        (add-guards-as-assertions-svga)))

; The following may take a couple of minutes.
(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system)))

(local (progn!
        (set-raw-mode t)
        (add-guards-as-assertions-all)))

; This should go pretty quickly.
(encapsulate
  ()
  (local (progn! (assign ld-okp t)
                 (mini-proveall))))

; The rest of these take longer.

(set-rewrite-stack-limit nil) ; implicitly local

(encapsulate
  ()
  (local
   (progn!
    (assign ld-okp t)
    (ld "workshops/2004/legato/support/proof-by-generalization-mult.lisp"
        :dir :system :ld-error-action :error))))

(encapsulate
  ()
  (local
   (progn!
    (assign ld-okp t)
    (ld "projects/hexnet/hexnet-model.lisp"
        :dir :system :ld-error-action :error))))

(encapsulate
  ()
  (local
   (progn!
    (assign ld-okp t)
    (ld "projects/apply/loop-tests.lisp"
        :dir :system :ld-error-action :error))))

; We can report results during both passes of certification.
; But note that we will not be able to include this book in
; a new session, because report-guard-checks will be undefined!
(progn! (set-raw-mode t)
        (report-guard-checks)
; Arrange that the report during the second pass of certification shows only
; the result of executing that pass.
        (zero-out-agaa-ht))
