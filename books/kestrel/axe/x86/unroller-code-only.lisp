; Using with-supporters to just get the code of the x86 Unrolling Lifter
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Including this book is much faster and brings in much less material than
;; including unroller.lisp.

;; WARNING: This book includes only the functions and rules needed to run the
;; unroller/lifter tool.  Users of this tool may want to include other books to
;; reason about the results of unrolling/lifting (e.g., books from
;; books/kestrel/bv/).

(include-book "centaur/misc/tshell" :dir :system) ; needs to be non-local since it has Raw Lisp code
(include-book "tools/with-supporters" :dir :system)

(defttag :unroller-x86-code-only)

(local (include-book "rule-lists")) ; defines the rule-lists mentioned below

;; TODO: Can this be sped up?
(make-event
  `(acl2::with-supporters
     (local (include-book "unroller"))
     :tables (:known-booleans-table)
     :names (def-unrolled
              ;; names mentioned in the macro def-unrolled:
              def-unrolled-fn
              print-level-at-least-tp
              make-event-quiet maybe-remove-temp-dir
              ;; Rules needed by the unroller:
              ,@(all-unroller-rules)
              ;; Functions used by the unroller
              ,@(symbolic-execution-rules32)
              ,@(symbolic-execution-rules64)
              ,@(symbolic-execution-rules-with-stop-pcs32)
              ,@(symbolic-execution-rules-with-stop-pcs64)
              ;; Names commonly needed in proofs:
              *standard-flags*
              ;; Names of rule-lists, to enable:
              register-aliases32
              register-aliases64
              ;; Rules needed for proofs:
              x::cf-spec8-becomes-getbit
              x::cf-spec16-becomes-getbit
              x::cf-spec32-becomes-getbit
              x::cf-spec64-becomes-getbit
              x::pf-spec8-becomes-bvcount
              x::pf-spec16-becomes-bvcount
              x::pf-spec32-becomes-bvcount
              x::pf-spec64-becomes-bvcount
              x::sf-spec8-becomes-getbit
              x::sf-spec16-becomes-getbit
              x::sf-spec32-becomes-getbit
              x::sf-spec64-becomes-getbit
              x::add-af-spec8-becomes-bvlt
              x::add-af-spec16-becomes-bvlt
              x::add-af-spec32-becomes-bvlt
              x::add-af-spec64-becomes-bvlt
              x::adc-af-spec8-becomes-bvlt
              x::adc-af-spec16-becomes-bvlt
              x::adc-af-spec32-becomes-bvlt
              x::adc-af-spec64-becomes-bvlt
              x::sub-af-spec8-becomes-bvlt
              x::sub-af-spec16-becomes-bvlt
              x::sub-af-spec32-becomes-bvlt
              x::sub-af-spec64-becomes-bvlt
              x86isa::sub-cf-spec8-opener
              x86isa::sub-cf-spec16-opener
              x86isa::sub-cf-spec32-opener
              x86isa::sub-cf-spec64-opener
              x::sub-pf-spec8-becomes-bvcount
              x::sub-pf-spec16-becomes-bvcount
              x::sub-pf-spec32-becomes-bvcount
              x::sub-pf-spec64-becomes-bvcount
              x::sbb-af-spec8-becomes-bvlt
              x::sbb-af-spec16-becomes-bvlt
              x::sbb-af-spec32-becomes-bvlt
              x::sbb-af-spec64-becomes-bvlt)))

;; To support proofs about lifted code
(in-theory (disable ;; rgfi ; rgfi may be used when the register name is not constant.  let's open it to XR
;             xr xw
             ))

;; todo: for reasoning about the result, we may want rules like cf-spec8-becomes-getbit
