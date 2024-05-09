; Top book for tools/ directory
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that most users should probably include only the individual tools they
;; need, rather than this top.lisp book.

(include-book "advise")
;(include-book "book-conflicts/bookdata-types")
;(include-book "book-conflicts/conflicts")
;(include-book "bstar") ; just a stub
;(include-book "btree") ; name conflict on flatten
(include-book "case-splitting-rules")
;(include-book "clone-stobj") ; just a stub
(include-book "cws")
(include-book "dead-events")
(include-book "defevaluator-fast")
(include-book "def-functional-instance")
(include-book "defined-const")
(include-book "define-keyed-function")
(include-book "defmacfun")
(include-book "defsum")
(include-book "defthmg")
;(include-book "defttag-muffled") ; suppresses ttag warnings
(include-book "deftuple")
(include-book "do-not")
(include-book "easy-simplify")
(include-book "equality-with-hons-copy")
(include-book "er-soft-logic")
(include-book "fake-event")
(include-book "flag")
;(include-book "flag-tests")
(include-book "include-an-arithmetic-book")
(include-book "include-raw")
;; (include-book "in-raw-mode") ; name conflict on in-raw-mode with manual (books/hacking/hacker.lisp)
(include-book "k-induction")
(include-book "last-theory-change")
(include-book "lint")
(include-book "match-tree")

;; This book memoizes some functions, so we undo that with unmemoize-lst. That
;; avoids the increased memory use and garbage collection time associated with
;; memoization:
(include-book "memoize-prover-fns")
(unmemoize-lst (f-get-global 'memoized-prover-fns state))

(include-book "mv-nth")
(include-book "names-after")
(include-book "nld")
(include-book "open-trace-file-bang")
(include-book "oracle-eval")
(include-book "oracle-eval-real")
(include-book "oracle-timelimit")
;(include-book "oracle-timelimit-tests")
(include-book "oracle-time")
;(include-book "oracle-time-tests")
(include-book "pattern-match")
(include-book "plev-ccl")
(include-book "plev")
;(include-book "prettygoals/portcullis")
;(include-book "prettygoals/top") ; redefines system function prettyify-clause
(include-book "prettygoals/doc")
(include-book "prove-dollar")
;(include-book "prove-dollar-tests")
(include-book "removable-runes")
(include-book "remove-hyps")
(include-book "rewrite-dollar-book")
(include-book "rewrite-dollar")
(include-book "rewrite-with-equality")
(include-book "rulesets")
(include-book "run-script")
(include-book "safe-case")
(include-book "saved-errors")
(include-book "save-obligs")
(include-book "some-events")
(include-book "stobj-frame")
;; (include-book "stobj-help") ; name clash with manual on LEN-RESIZE-LIST
(include-book "symlet")
(include-book "table-replay")
(include-book "templates")
(include-book "theory-tools")
(include-book "time-dollar-with-gc")
(include-book "trivial-ancestors-check")
(include-book "types-misc")
(include-book "untranslate-for-exec")
;(include-book "untranslate-for-exec-tests")
(include-book "with-arith1-help")
(include-book "with-arith5-help")
(include-book "with-arith-help")
(include-book "without-subsumption")
(include-book "with-quoted-forms")
(include-book "with-supporters-doc")
(include-book "with-supporters")
;(include-book "with-supporters-test-sub")
;(include-book "with-supporters-test-top")

