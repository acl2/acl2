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

; Although one should not include "parse-leotests" in general,
; in the case of the current book, it is analogous to parse-leotests.
; (Try not to include the current book in other books!)
(include-book "parse-leotests")

(include-book "../testing/executing-leotests")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run an exec test suite, and gather overall time information.

; A test suite is a leotest-file-listp; we might want to add structure
; around that for overall properties such as intended platorm.
; Returns a value of type leotest-suite-exec-outcomes.

(define run-exec-test-suite ((test-suite leotest-file-listp) state)
  :returns (mv (outcome leotest-suite-exec-outcomesp) state)
  (b* (((mv start-ut state) (oslib::universal-time state))
       ((mv start-timestamp state) (oslib::date state))
       (outcomes (run-exec-leotest-files test-suite))
       ((mv end-timestamp state) (oslib::date state))
       ((mv end-ut state) (oslib::universal-time state)))
    (mv (make-leotest-suite-exec-outcomes
         :start-time start-timestamp
         :end-time end-timestamp
         :elapsed-time (- end-ut start-ut)
         :outcomes outcomes)
        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test-executor-on-leotests

; Given a root directory,
; * finds all the ".leo" "leotest" files starting with that path (sorted)
;   (a leotest file has a block comment with a mini-yaml spec of what
;   component it is testing)
;   Note, at the present time, it is really only tests marked
;     "namespace: Compile; expectation: Pass"
;   that make sense to execute.
; * parses/scans all the leotest files into values of the leotest-file type;
;   for each leotest file, also parses and abstracts to AST the input files
;   referenced in the block comment
; * runs all the tests described by those values of type leotest-file.
;
(define test-executor-on-leotests ((leo-root-dir stringp) state)
  (b* (;; for now, just restrict leo-root-dir to start and end with slash
       ((unless (and (str::strprefixp "/" leo-root-dir)
                     (str::strsuffixp "/" leo-root-dir)))
        (raise "test-parser-on-leotests: leo-root-dir must start and end with slash")
        state)
       ((mv leotest-filenames state) (all-leo-test-files leo-root-dir state))
       ;; First scan the test file to get the header info and the body.
       ;; Does not invoke leo parser.
       ((mv all-leotest-files state)
        (leotest-parse-files-at-paths leo-root-dir leotest-filenames state))
       ;; Filter out all but "namespace: Compile; expectation: Pass"
       (leotest-files (leotest-files-filter all-leotest-files
                                            (list (leotest-category-compile))
                                            (list t))) ; t means pass
       ((mv test-suite-outcome state) (run-exec-test-suite leotest-files state))
       ;; NOTE: for now leave in this print statement.
       ;; We can comment it out when the number of failures nears zero.
       (- (cw "test-suite-outcome = ~x0~%" test-suite-outcome))
       (- (report-exec-leotests test-suite-outcome)))
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example:
; (test-executor-on-leotests "/home/yourname/leo/tests/" state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
