; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser-interface")
(include-book "printer")
(include-book "oslib/ls" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "std/strings/suffixp" :dir :system)
(include-book "std/typed-lists/string-listp" :dir :system)

(acl2::controlled-configuration :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-directory-utilities
  :parents (parsing-and-printing)
  :short "Bulk parser-runner for assurance testing."
  :long
  (xdoc::topstring
   (xdoc::p
    "@(tsee parse-directory-files) takes the path of a directory, finds all
     regular files in it whose names end in @('.remora'), runs
     @(tsee parse-from-file) on each, and prints a summary to the comment
     window: @('PASS') / @('FAIL') per file, plus the total count of each.")
   (xdoc::p
    "It returns a structured record (a property list) so callers can also
     inspect the result programmatically &mdash; e.g., the list of failing
     files paired with their @(see reserr) values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dot-remora-files ((files string-listp))
  :returns (remora-files string-listp)
  :short "Filter a list of file names to those ending in @('.remora')."
  (cond ((endp files) nil)
        ((str::strsuffixp ".remora" (str-fix (car files)))
         (cons (str-fix (car files))
               (dot-remora-files (cdr files))))
        (t (dot-remora-files (cdr files)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-each-remora-file ((directory stringp)
                                (files string-listp)
                                (n-pass natp)
                                (n-fail natp)
                                (errors true-listp)
                                state)
  :returns (mv (npass natp)
               (nfail natp)
               (errs true-listp)
               state)
  :hooks nil
  :short "Tail-recursive driver for @(tsee parse-directory-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Walks the list of file names, calling @(tsee parse-from-file) on
     each (under @('directory')), and tallies passes and failures.  Prints a
     @('PASS')/@('FAIL') marker per file via @(tsee cw).
     Each failure entry in the returned @('errors') list is a cons pair
     @('(filename . reserr)')."))
  (b* (((when (endp files))
        (mv (lnfix n-pass) (lnfix n-fail) (rev errors) state))
       (file (str-fix (car files)))
       (path (oslib::catpath directory file))
       ((mv ast state) (parse-from-file path state))
       ((when (reserrp ast))
        (b* ((- (cw "FAIL: ~s0~%" file)))
          (parse-each-remora-file directory
                                  (cdr files)
                                  n-pass
                                  (+ 1 (lnfix n-fail))
                                  (cons (cons file ast) errors)
                                  state)))
       (- (cw "PASS: ~s0~%" file)))
    (parse-each-remora-file directory
                            (cdr files)
                            (+ 1 (lnfix n-pass))
                            n-fail
                            errors
                            state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-directory-files ((directory stringp) state)
  :returns (mv summary state)
  :hooks nil
  :short "Parse all @('.remora') files in a directory, printing a summary."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lists regular files in @('directory') (via @(tsee oslib::ls-files)),
     keeps those ending in @('.remora'), and runs
     @(tsee parse-from-file) on each.  Prints @('PASS')/@('FAIL') per file
     plus a final summary line to the comment window.  Returns a
     property list of the form
     @({
       (:directory <path>
        :total <n>
        :passed <n>
        :failed <n>
        :errors ((<filename> . <reserr>) ...))
     })
     for programmatic inspection.")
   (xdoc::p
    "On a directory listing failure, prints the error and returns
     @('(:error <error-msg>)')."))
  (b* (((mv err files state) (oslib::ls-files directory))
       ((when err)
        (b* ((- (cw "Error listing directory ~s0: ~@1~%" directory err)))
          (mv (list :error err) state)))
       (remora-files (dot-remora-files files))
       ((mv n-pass n-fail errors state)
        (parse-each-remora-file directory remora-files 0 0 nil state))
       (total (+ (lnfix n-pass) (lnfix n-fail)))
       (- (cw "~%Parsed ~x0 .remora file~s1 in ~s2: ~x3 passed, ~x4 failed.~%"
              total
              (if (= total 1) "" "s")
              directory
              n-pass
              n-fail)))
    (mv (list :directory directory
              :total total
              :passed n-pass
              :failed n-fail
              :errors errors)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; parse-print-parse: round-trip testing.  For each file, runs the
;; one-and-a-half round trip:
;;
;;   1. parse the file to an AST    (failure stage :parse1)
;;   2. print the AST to text       (failure stage :print)
;;   3. parse the printed text      (failure stage :parse2)
;;   4. compare the two ASTs        (failure stage :compare)
;;
;; A file passes only if all four stages succeed and the second AST
;; equals the first.  This is a concrete instance of the round-trip
;; theorem for the asts produced by these source files.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-print-parse-each-remora-file ((directory stringp)
                                             (files string-listp)
                                             (n-pass natp)
                                             (n-fail natp)
                                             (errors true-listp)
                                             state)
  :returns (mv (npass natp)
               (nfail natp)
               (errs true-listp)
               state)
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable filep-when-result-not-error)))
  :short "Tail-recursive driver for @(tsee parse-print-parse-directory-files)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Walks the list of file names, performing the four-stage round-trip
     on each.  Each failure entry in the returned @('errors') list is a
     pair @('(filename :stage <kw> :info <data>)') where @('<kw>') is
     one of @(':parse1'), @(':print'), @(':parse2'), or @(':compare').
     Prints @('PASS') / @('FAIL[<stage>]') per file."))
  (b* (((when (endp files))
        (mv (lnfix n-pass) (lnfix n-fail) (rev errors) state))
       (file (str-fix (car files)))
       (path (oslib::catpath directory file))
       ;; Stage 1: parse the file.
       ((mv ast1 state) (parse-from-file path state))
       ((when (reserrp ast1))
        (b* ((- (cw "FAIL[parse1]: ~s0~%" file)))
          (parse-print-parse-each-remora-file
           directory
           (cdr files)
           n-pass
           (+ 1 (lnfix n-fail))
           (cons (list file :stage :parse1 :info ast1) errors)
           state)))
       ;; Stage 2: print the AST.  print-file is total, but we still
       ;; check stringp defensively in case the result type changes.
       (printed (print-file ast1))
       ((unless (stringp printed))
        (b* ((- (cw "FAIL[print]: ~s0~%" file)))
          (parse-print-parse-each-remora-file
           directory
           (cdr files)
           n-pass
           (+ 1 (lnfix n-fail))
           (cons (list file :stage :print :info printed) errors)
           state)))
       ;; Stage 3: re-parse the printed text.
       (ast2 (parse-from-string printed))
       ((when (reserrp ast2))
        (b* ((- (cw "FAIL[parse2]: ~s0~%" file)))
          (parse-print-parse-each-remora-file
           directory
           (cdr files)
           n-pass
           (+ 1 (lnfix n-fail))
           (cons (list file :stage :parse2
                       :info (list :reserr ast2 :printed printed))
                 errors)
           state)))
       ;; Stage 4: ASTs should be equal.
       ((unless (equal ast1 ast2))
        (b* ((- (cw "FAIL[compare]: ~s0~%" file)))
          (parse-print-parse-each-remora-file
           directory
           (cdr files)
           n-pass
           (+ 1 (lnfix n-fail))
           (cons (list file :stage :compare
                       :info (list :ast1 ast1 :ast2 ast2 :printed printed))
                 errors)
           state)))
       (- (cw "PASS: ~s0~%" file)))
    (parse-print-parse-each-remora-file directory
                                        (cdr files)
                                        (+ 1 (lnfix n-pass))
                                        n-fail
                                        errors
                                        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-print-parse-directory-files ((directory stringp) state)
  :returns (mv summary state)
  :hooks nil
  :short "One-and-a-half round-trip test on every @('.remora') file in
          a directory: parse, print, re-parse, compare."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lists regular files in @('directory') (via @(tsee oslib::ls-files)),
     keeps those ending in @('.remora'), and runs the four-stage
     round-trip on each: parse-from-file &rarr; print-file &rarr;
     parse-from-string &rarr; @(tsee equal).  Prints @('PASS') or
     @('FAIL[<stage>]') per file plus a summary line.")
   (xdoc::p
    "Returns a property list of the form
     @({
       (:directory <path>
        :total <n>
        :passed <n>
        :failed <n>
        :errors ((<filename> :stage <kw> :info <data>) ...))
     })
     The @('<stage>') is one of @(':parse1'), @(':print'),
     @(':parse2'), or @(':compare').  The @(':info') content depends
     on the stage: a @(tsee reserrp) value for the parse failures, the
     printed text plus the failing reserr for @(':parse2'), and both
     ASTs plus the printed text for @(':compare')."))
  (b* (((mv err files state) (oslib::ls-files directory))
       ((when err)
        (b* ((- (cw "Error listing directory ~s0: ~@1~%" directory err)))
          (mv (list :error err) state)))
       (remora-files (dot-remora-files files))
       ((mv n-pass n-fail errors state)
        (parse-print-parse-each-remora-file
         directory remora-files 0 0 nil state))
       (total (+ (lnfix n-pass) (lnfix n-fail)))
       (- (cw "~%Round-tripped ~x0 .remora file~s1 in ~s2: ~x3 passed, ~x4 failed.~%"
              total
              (if (= total 1) "" "s")
              directory
              n-pass
              n-fail)))
    (mv (list :directory directory
              :total total
              :passed n-pass
              :failed n-fail
              :errors errors)
        state)))
