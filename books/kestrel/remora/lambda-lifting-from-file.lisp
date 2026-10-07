; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "lambda-lifting")
(include-book "parser-interface")
(include-book "parse-error-printing")
(include-book "pretty-printer")
(include-book "kestrel/utilities/widen-margins" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file-I/O entry point for lambda lifting.  It is kept in a
; separate book from lambda-lifting.lisp so that the core lambda-lifting logic
; does not have to depend on (and pay the certification-load cost of) the
; parser and printer.

(define lambda-lift-from-file ((filename stringp) state)
  :parents (lambda-lifting)
  :returns (mv (successp booleanp) state)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable filep-when-result-not-error)))
  :short "Parse a Remora source file, lambda-lift it,
          and print the result."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a development and testing convenience:
     it lets one run lambda lifting on a source file
     and inspect the printed result.
     No other code depends on it.")
   (xdoc::p
    "Parses the Remora source file @('filename')
     (via @(tsee parse-from-file)),
     makes its binder names distinct with @(tsee file-uniquify-names),
     as the guard of @(tsee lambda-lift-file) requires,
     lambda-lifts it with @(tsee lambda-lift-file), and prints the
     resulting file with @(tsee pretty-print-file)
     (at 100 columns) --- unless
     uniquification and lambda lifting together left the
     file unchanged, in which case nothing is printed.  Returns
     @('(mv successp state)'), where @('successp') is @('t') unless
     parsing fails, in which case it is @('nil')."))
  (b* (((mv ast state) (parse-from-file filename state))
       ((when (reserrp ast))
        (b* ((- (cw "Parse error in ~s0:~%" filename))
             (- (print-parse-error ast)))
          (mv nil state)))
       (new-file (lambda-lift-file (file-uniquify-names ast)))
       ((when (equal new-file ast))
        (b* ((- (cw "No change after lambda lifting ~s0.~%" filename)))
          (mv t state)))
       ;; Widen the fmt margins so that cw does not re-wrap the printed
       ;; lines (it would otherwise break lines past column 70 or so).
       (state (acl2::widen-margins state))
       (- (cw "~s0~%" (pretty-print-file new-file :width 100)))
       (state (acl2::unwiden-margins state)))
    (mv t state)))
