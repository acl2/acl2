; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This books runs (add-guards-as-assertions-all), which checks top-level calls
; of built-in functions that are in :logic mode, guard-verified.  That check is
; done on (mini-proveall) after a more limited check,
; (add-guards-as-assertions-svga), checks just those functions that are
; guard-verified outside the system, i.e., are in *system-verify-guards-alist*.

; Those checks can be done without this book, by just loading its workhorse,
; check-system-guards-raw.lsp, as follows.  First do the set-up:

; :q
; (load "check-system-guards-raw.lsp")
; (add-guards-as-assertions-all)
; (lp)

; Now execute some forms, e.g.:

; (mini-proveall)
; :ubt 1
; (time$ (include-book "arithmetic/top" :dir :system))

; Finally, to see that guards were indeed being checked:

; :q
; (report-guard-checks)

; This book does some of that automatically, as a bit of a check during
; regression on guards of guard-verified system functions.

; One can do more, for example as follows.

#||
(value :q)
(load "check-system-guards-raw.lsp")
(add-guards-as-assertions-all)
(lp)
(set-rewrite-stack-limit nil)
; This may cause a stack overflow, but that's OK.
(ld ; linebreak to avoid warning during regression
 "../workshops/2004/legato/support/proof-by-generalization-mult.lisp") ; ;
(ubt 1)
(ld ; linebreak to avoid warning during regression
 "../projects/hexnet/hexnet-model.lisp")
(value :q)
(report-guard-checks) ; should show lots of checking
||#

; (depends-on "check-system-guards-raw.lsp")

(in-package "ACL2")

(local (include-book "tools/include-raw" :dir :system))

(defttag :check-system-guards)

(local (include-raw "check-system-guards-raw.lsp"))

(local (progn!
        (set-raw-mode t)
        (add-guards-as-assertions-svga)))

; The following may take a couple of minutes.
(local (include-book "arithmetic-5/top" :dir :system))

(local (progn!
        (set-raw-mode t)
        (add-guards-as-assertions-all)))

; This should go quickly.
(local (progn! (assign ld-okp t)
               (mini-proveall)))

; We can report results during both passes of certification.
; But note that we will not be able to include this book in
; a new session, because report-guard-checks will be undefined!
(progn! (set-raw-mode t)
        (report-guard-checks))
