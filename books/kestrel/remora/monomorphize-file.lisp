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

(define monomorphize-file ((filename stringp) state)
  :parents (monomorphize)
  :returns (mv result state)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable progp-when-result-not-error)))
  :short "Parse a Remora file, monomorphize it, and print the result."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the Remora program in @('filename') (via @(tsee parse-from-file)),
     monomorphizes it with @(tsee monomorphize-prog), and prints the resulting
     program with @(tsee print-prog) --- unless monomorphization left the
     program unchanged, in which case nothing is printed.  Returns
     @('(mv result state)'), where @('result') is the monomorphized
     @(tsee prog), or the input @(tsee prog) when it is unchanged, or a
     @(tsee reserrp) when parsing fails."))
  (b* (((mv ast state) (parse-from-file filename state))
       ((when (reserrp ast))
        (b* ((- (cw "Parse error in ~s0: ~x1~%" filename ast)))
          (mv ast state)))
       ((mv err & new-prog) (monomorphize-prog ast))
       ((when err)
        (b* ((- (cw "Monomorphizing ~s0 failed: ~x1~%" filename err)))
          (mv ast state)))
       ((when (equal new-prog ast))
        (b* ((- (cw "No change after monomorphizing ~s0.~%" filename)))
          (mv ast state)))
       (- (cw "~s0~%" (print-prog new-prog))))
    (mv new-prog state)))
