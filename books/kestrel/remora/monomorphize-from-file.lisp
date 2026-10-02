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
(include-book "parse-error-printing")
(include-book "pretty-printer")
(include-book "kestrel/utilities/widen-margins" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file-I/O entry point for monomorphization.  It is kept in a
; separate book from monomorphize.lisp so that the core monomorphization logic
; does not have to depend on (and pay the certification-load cost of) the
; parser and printer.

(define monomorphize-from-file ((filename stringp) state)
  :parents (monomorphize)
  :returns (mv (successp booleanp) state)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable filep-when-result-not-error)))
  :short "Parse a Remora source file, monomorphize it,
          and print the result."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a development and testing convenience:
     it lets one run the monomorphizer on a source file
     and inspect the printed result.
     No other code depends on it.")
   (xdoc::p
    "Parses the Remora source file @('filename')
     (via @(tsee parse-from-file)),
     monomorphizes it with @(tsee monomorphize-file), and prints the
     resulting file with @(tsee pretty-print-file)
     (at 100 columns) --- unless
     monomorphization left the
     file unchanged, in which case nothing is printed.  Returns
     @('(mv successp state)'), where @('successp') is @('t') unless
     parsing or monomorphization fails, in which case it is @('nil').")
   (xdoc::p
    "This is program-level monomorphization, corresponding to the
     implementation's @('Monomorphize.monomorphize'): the instances of
     the definitions that are instantiated are hoisted into new @('def')
     declarations, replacing the polymorphic definitions they come from.
     The file must have no imports; see @(tsee monomorphize-file), whose
     errors (including @(':imports-not-supported')) are reported here."))
  (b* (((mv ast state) (parse-from-file filename state))
       ((when (reserrp ast))
        (b* ((- (cw "Parse error in ~s0:~%" filename))
             (- (print-parse-error ast)))
          (mv nil state)))
       ((mv err new-file) (monomorphize-file ast))
       ((when err)
        (b* ((- (cw "Monomorphizing ~s0 failed: ~x1~%" filename err)))
          (mv nil state)))
       ((when (equal new-file ast))
        (b* ((- (cw "No change after monomorphizing ~s0.~%" filename)))
          (mv t state)))
       ;; Widen the fmt margins so that cw does not re-wrap the printed
       ;; lines (it would otherwise break lines past column 70 or so).
       (state (acl2::widen-margins state))
       (- (cw "~s0~%" (pretty-print-file new-file :width 100)))
       (state (acl2::unwiden-margins state)))
    (mv t state)))
