; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "monomorphize")
(include-book "parser-interface")
(include-book "printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file-I/O entry point for monomorphization.  It is kept in a
; separate book from monomorphize.lisp so that the core monomorphization logic
; does not have to depend on (and pay the certification-load cost of) the
; parser and printer.

(define monomorphize-from-file ((filename stringp) state)
  :parents (monomorphize)
  :returns (mv result state)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable exprp-when-result-not-error)))
  :short "Parse a Remora expression file, monomorphize it,
          and print the result."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a development and testing convenience:
     it lets one run the monomorphizer on a source file
     and inspect the printed result.
     No other code depends on it.")
   (xdoc::p
    "Parses the standalone Remora expression in @('filename')
     (via @(tsee parse-top-exp-from-file)),
     monomorphizes it with @(tsee monomorphize-top-expr), and prints the
     resulting expression with @(tsee print-expr) --- unless
     monomorphization left the
     expression unchanged, in which case nothing is printed.  Returns
     @('(mv result state)'), where @('result') is the monomorphized
     @(tsee expr), or the input @(tsee expr) when it is unchanged, or a
     @(tsee reserrp) when parsing fails.")
   (xdoc::p
    "The file must contain a standalone expression
     (the input format of the implementation's @('monomorphize -e')):
     the model's monomorphizer is expression-level,
     corresponding to the implementation's @('monomorphizeExp').
     Source files with declarations are not supported;
     they require program-level monomorphization
     (the implementation's @('Monomorphize.monomorphize'),
     which hoists the collected instance bindings
     as new @('def') declarations),
     which the model does not have."))
  (b* (((mv ast state) (parse-top-exp-from-file filename state))
       ((when (reserrp ast))
        (b* ((- (cw "Parse error in ~s0: ~x1~%" filename ast)))
          (mv ast state)))
       ((mv err & new-expr) (monomorphize-top-expr ast))
       ((when err)
        (b* ((- (cw "Monomorphizing ~s0 failed: ~x1~%" filename err)))
          (mv ast state)))
       ((when (equal new-expr ast))
        (b* ((- (cw "No change after monomorphizing ~s0.~%" filename)))
          (mv ast state)))
       (- (cw "~s0~%" (print-expr new-expr))))
    (mv new-expr state)))
