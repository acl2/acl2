; Standard System Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arity")
(include-book "arity-plus")
(include-book "defchoose-queries")
(include-book "definedp")
(include-book "definedp-plus")
(include-book "defun-sk-queries")
(include-book "formals-plus")
(include-book "fundef-disabledp")
(include-book "fundef-enabledp")
(include-book "get-measure")
(include-book "get-measure-plus")
(include-book "get-ruler-extenders")
(include-book "get-ruler-extenders-plus")
(include-book "get-well-founded-relation")
(include-book "get-well-founded-relation-plus")
(include-book "guard-theorem-no-simplify")
(include-book "guard-theorem-no-simplify-dollar")
(include-book "guard-verified-p")
(include-book "guard-verified-p-plus")
(include-book "ibody")
(include-book "induction-machine")
(include-book "induction-machine-plus")
(include-book "irecursivep")
(include-book "irecursivep-plus")
(include-book "measured-subset")
(include-book "measured-subset-plus")
(include-book "no-stobjs-p")
(include-book "no-stobjs-p-plus")
(include-book "non-executablep")
(include-book "non-executablep-plus")
(include-book "number-of-results")
(include-book "number-of-results-plus")
(include-book "primitivep")
(include-book "primitivep-plus")
(include-book "pure-raw-p")
(include-book "rawp")
(include-book "recursive-calls")
(include-book "stobjs-in-plus")
(include-book "stobjs-out-plus")
(include-book "tail-recursive-p")
(include-book "termination-theorem-dollar")
(include-book "ubody")
(include-book "ubody-plus")
(include-book "uguard")
(include-book "uguard-plus")
(include-book "unwrapped-nonexec-body")
(include-book "unwrapped-nonexec-body-plus")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/function-queries
  :parents (std/system)
  :short "Utilities to query functions."
  :long
  (xdoc::topstring-p
   "These utilities are mostly for named functions in the @(see world),
    but some utilities also work on lambda expressions."))
