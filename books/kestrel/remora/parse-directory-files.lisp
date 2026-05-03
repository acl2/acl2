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
(include-book "oslib/ls" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "std/strings/suffixp" :dir :system)
(include-book "std/typed-lists/string-listp" :dir :system)

(acl2::controlled-configuration :no-function nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parse-directory-utilities
  :parents (remora)
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

(define keep-remora-files ((files string-listp))
  :returns (remora-files string-listp)
  :short "Filter a list of file names to those ending in @('.remora')."
  (cond ((endp files) nil)
        ((str::strsuffixp ".remora" (str-fix (car files)))
         (cons (str-fix (car files))
               (keep-remora-files (cdr files))))
        (t (keep-remora-files (cdr files)))))

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
    "Walks the list of file names, calling @(tsee parse-from-file) on each
     (under @('directory')), and tallies passes and failures.  Prints a
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
     filters to those ending in @('.remora'), and runs
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
       (remora-files (keep-remora-files files))
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
