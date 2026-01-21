; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "oslib/date" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/suffixp" :dir :system)
(include-book "std/strings/strtok" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "std/osets/sort" :dir :system)

(include-book "../testing/parsing-leotests")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Finding the leo test files.

; Try not to include the current book in other books.
; This is why:
; * To run the ACL2 parser on the /leo/ tests, we need to look through the
;   filesystem for the .leo files under ../leo/tests/.
; * In order to include "cl-directory", we need to have a trust tag mentioned
;   by the .acl2 version of the current file.
;   (If we used sys-call+, then in order to compile the call to
;   sys-call+ we would need a trust tag defined in this book.)
; * Any book that uses this book will also need to mention the trust tag in
;   its .acl2 file.
; To reduce the number of things dependent on the trust tag,
; we recommend not including the current book in other books
; unless unavoidable.

(include-book "cl-directory")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; remove-specials

; These are "special" in the sense that there is something wrong with the .leo
; files and we need to filter them out.

; compiler/_group/...
; have a lot of .leo files with no namespace or expectation indicators

; Note: consider profiling this.  It seems to take a long time to be admitted.
(define remove-specials ((filenames string-listp))
  :returns (ret-filenames string-listp)
  (if (or (endp filenames) (not (stringp (car filenames))))
      (prog2$ (cw "~%WARNING: not currently running tests in _group, import,
  inputs, serialize, or additional_benches.~%")
              nil)
    (if (or (str::substrp "/_group/" (first filenames)) ; incorrect annotations
            (str::substrp "/import/"  (first filenames))
            (str::substrp "/inputs/"  (first filenames))
            (str::substrp "/serialize/"  (first filenames))
            (str::substrp "/additional_benches/"  (first filenames)))
        (remove-specials (rest filenames))
      (str::string-list-fix
       (cons (first filenames) (remove-specials (rest filenames)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; all-leo-test-files

; leo-root-dir must start and end with "/".
; Finds all "*.leo" files under leo-root-dir.
; The paths returned are relative to leo-root-dir.
;
; For consistency of results, it would be good if the
; root dir ends in "/leo/tests/" so that the directories
; in the returned paths have just the needed content.

(define all-leo-test-files ((leo-root-dir stringp) state)
  :returns (mv (leo-test-files string-listp) state)
  (b* (((unless (stringp leo-root-dir))
        (raise "all-leo-test-files: argument must be string.")
        (mv nil state))
       ((unless (and (str::strprefixp "/" leo-root-dir)
                     (str::strsuffixp "/" leo-root-dir)))
        (raise "all-leo-test-files: argument must start and end with slashes.")
        (mv nil state))
       (filenames (acl2::cl-directory-relative leo-root-dir "**/*.leo"))
       (ordered-filenames (set::mergesort filenames))
       ((unless (string-listp ordered-filenames))
        (raise "leo-test-file-list: expected list of strings from set::mergesort")
        (mv nil state))
       ;; hack to remove filenames with problems
       (no-specials (remove-specials (str::string-list-fix ordered-filenames)))
       ((unless (string-listp no-specials))
        (raise "leo-test-file-list: expected list of strings from set::mergesort")
        (mv nil state)))
    (mv no-specials state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a parse test suite, and gather overall time information.

; A test suite is a leotest-file-listp; we might want to add structure
; around that for overall properties such as intended platorm.
; Returns a value of type leotest-suite-parse-outcomes.

(define run-parse-test-suite ((test-suite leotest-file-listp) state)
  :returns (mv (outcome leotest-suite-parse-outcomesp) state)
  (b* (((mv start-ut state) (oslib::universal-time state))
       ((mv start-timestamp state) (oslib::date state))
       (outcomes (run-parse-leotest-files test-suite))
       ((mv end-timestamp state) (oslib::date state))
       ((mv end-ut state) (oslib::universal-time state)))
    (mv (make-leotest-suite-parse-outcomes
         :start-time start-timestamp
         :end-time end-timestamp
         :elapsed-time (- end-ut start-ut)
         :outcomes outcomes)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test-parser-on-leotests

; Given a root directory,
; * finds all the ".leo" "leotest" files starting with that path (sorted)
;   (a leotest file has a block comment with a mini-yaml spec of what parser
;   component it is testing);
; * parses all the leotest files into values of the leotest-file type;
; * runs all the tests described by those values of type leotest-file,
;   collecting the outcome information into a value of type
;   leotest-suite-parse-outcomes;
; * outputs a report to stdout about the oucomes.

(define test-parser-on-leotests ((leo-root-dir stringp) state)
  (b* (;; for now, just restrict leo-root-dir to start and end with slash
       ((unless (and (str::strprefixp "/" leo-root-dir)
                     (str::strsuffixp "/" leo-root-dir)))
        (raise "test-parser-on-leotests: leo-root-dir must start and end with slash")
        state)
       ((mv leotest-filenames state) (all-leo-test-files leo-root-dir state))
       ;; First parse the test file headers and scan the contents.
       ;; Does not invoke leo parser.
       ((mv leotest-files state) (leotest-parse-files-at-paths leo-root-dir leotest-filenames state))
       ((mv test-suite-outcome state) (run-parse-test-suite leotest-files state))
       (- (report-parse-leotests test-suite-outcome)))
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example:
; (test-parser-on-leotests "/home/yourname/leo/tests/" state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
