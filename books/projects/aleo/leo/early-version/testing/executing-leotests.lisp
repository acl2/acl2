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

(include-book "parsing-leotests")

(include-book "../definition/compiler")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we introduce code to run the ACL2 Leo executor over the leo test files.
; First we define data types to capture the test outcomes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcome of executing a single leo test case.
; Does not store the category (ie. namespace) or passp (expectation)
; since those are file-level attributes.

(fty::defprod leotest-testcase-exec-outcome
  ((testcase leotest-testcasep) ; this duplicates the testcase, for convenience
   (skip? bool) ; if this test is not applicable for an exec test---
                ; for example, a namespace: Compiler expectation: Fail test
                ; could be expected to fail due to type checking, not due to parsing,
                ; so we should really skip it for parsing.
   (ok? bool) ; T means the test did the right thing.
              ; If it is a must-fail test, T means the exec failed.
   ;; consider adding optional time and space measures
  )
  :pred leotest-testcase-exec-outcomep)

(fty::deflist leotest-testcase-exec-outcome-list
  :elt-type leotest-testcase-exec-outcome
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-testcase-exec-outcome-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcomes of parsing zero or more leotests in a leotest file.

(fty::defprod leotest-file-exec-outcomes
  (;; Now links to the file for file-level info such as
   ;; file name, category, and passp,
   ;; but we could copy those things to here and skip the link.
   (file-of-tests leotest-filep)
   (outcomes leotest-testcase-exec-outcome-list)
   ;; consider adding optional time and space measures
   ;; consider adding a timestamp per file here
  )
  :pred leotest-file-exec-outcomesp)

(fty::deflist leotest-file-exec-outcomes-list
  :elt-type leotest-file-exec-outcomes
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-file-exec-outcomes-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcomes of running the tests in a list of files.

(fty::defprod leotest-suite-exec-outcomes
  (;; consider adding leo version and commit
   ;; consider adding leo-acl2 commit, cl version
   (start-time string)
   (end-time string)
   (elapsed-time integerp)
   (outcomes leotest-file-exec-outcomes-listp))
  :pred leotest-suite-exec-outcomesp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run an exec test.
; Parses, compiles, and evaluates.

;; TODO: turn into function so it can get the right item string
(defconst *malformed-exec-info-outcome*
  (make-leotest-testcase-exec-outcome
   :testcase (make-leotest-testcase :item "??")
   :skip? nil
   :ok? nil))


(define malformed-exec-info-outcome ((testcase leotest-testcasep)
                                     (reason stringp))
  :returns (outcome leotest-testcase-exec-outcomep)
  (make-leotest-testcase-exec-outcome
   :testcase
   (make-leotest-testcase :item
                          (concatenate 'string
                                       reason
                                       (leotest-testcase->item
                                        testcase)))
   :skip? nil
   :ok? nil))

(define run-exec-leotest ((testcase leotest-testcasep)
                          (cat leotest-categoryp)
                          (passp booleanp))
  :returns (outcome leotest-testcase-exec-outcomep)
  ;; For now, requires that
  ;; * category is (leotest-category-compile),
  ;; * passp is T
  ;; * there is at an input file in tc.incontents (or at least
  ;;   it is a string, not NIL)
  (b* (((unless (and (equal cat (leotest-category-compile))
                     passp))
        (malformed-exec-info-outcome testcase "wrong category: "))
       ((leotest-testcase tc) testcase)
       ((unless (stringp tc.incontents))
        (malformed-exec-info-outcome testcase
                                     "incontents not a string, item: "))
       ((mv erp ?outlines)
        (compile-to-lines tc.item
                          tc.incontents
                          :edwards-bls12)))
    (make-leotest-testcase-exec-outcome
     :testcase testcase
     :skip? nil
     :ok? (not erp)))) ; we ignore outlines (the output lines) for now


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a list of similar tests

(define run-exec-leotests ((testcases leotest-testcase-listp)
                           (cat leotest-categoryp)
                           (passp booleanp))
  :returns (test-outcomes leotest-testcase-exec-outcome-listp)
  (if (endp testcases) nil
    (cons (run-exec-leotest (car testcases) cat passp)
          (run-exec-leotests (cdr testcases) cat passp))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run the tests defined in a leotest file

;; An exec test file has only one test body, unlike for parsing test files.
;; Below here we vary from the parse leotest pattern.

(define run-exec-leotest-file ((ltfile leotest-filep))
  :returns (file-outcomes leotest-file-exec-outcomesp)
  (b* (((leotest-file ltf) ltfile) ;creates ltf.path, etc.
       (outcomes (run-exec-leotests ltf.testcases
                                    ltf.category
                                    ltf.passp)))
    (make-leotest-file-exec-outcomes
     :file-of-tests ltfile
     :outcomes outcomes)))

; Quick unit test
; (mv-let (ltf state) (leotest-parse-file-at-path "~/leo/tests/compiler/statements/" "iteration_basic.leo" state) (mv (run-exec-leotest-file ltf) state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a list of files of tests

(define run-exec-leotest-files ((files leotest-file-listp))
  :returns (outcomes leotest-file-exec-outcomes-listp)
  (if (endp files) nil
    (cons (run-exec-leotest-file (car files))
          (run-exec-leotest-files (cdr files)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See also tests/parsing-leotests.lisp

; Running a test suite is defined in tests/exec-leotests.lisp
; because it fetches the system date, which requires a trust tag,
; and we are trying to limit trust tags to the leo-acl2/tests/ directory.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reporting

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Counting the number of passed and failed and skipped items

; Effectively unchanged from parse outcomes
; Consider ways to merge them.

(define count-pass/fail/skip-tests-items--exec ((outcomes leotest-testcase-exec-outcome-listp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (if (endp outcomes)
      (mv 0 0 0)
    (b* ((skip? (leotest-testcase-exec-outcome->skip? (first outcomes)))
         ((mv p f s) (if skip?
                         (mv 0 0 1)
                       (if (leotest-testcase-exec-outcome->ok? (first outcomes))
                           (mv 1 0 0)
                         (mv 0 1 0))))
         ((mv pn fn sn) (count-pass/fail/skip-tests-items--exec (rest outcomes))))
      (mv (+ p pn) (+ f fn) (+ s sn)))))

(define count-pass/fail/skip-tests-file--exec ((file leotest-file-exec-outcomesp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (count-pass/fail/skip-tests-items--exec
   (leotest-file-exec-outcomes->outcomes file)))

(define count-pass/fail/skip-tests-files--exec ((files leotest-file-exec-outcomes-listp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (if (endp files)
      (mv 0 0 0)
    (b* (((mv p f s) (count-pass/fail/skip-tests-file--exec (first files)))
         ((mv pn fn sn) (count-pass/fail/skip-tests-files--exec (rest files))))
      (mv (nfix (+ p pn)) (nfix (+ f fn)) (nfix (+ s sn))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List the failed test cases

(define report-failed-exec-leotests-for-testcase-outcome ((path stringp)
                                                          (passp booleanp)
                                                          (testcase-outcome leotest-testcase-exec-outcomep))
  (if (or (leotest-testcase-exec-outcome->ok? testcase-outcome)
          (leotest-testcase-exec-outcome->skip? testcase-outcome))
      nil
    (progn$ (cw "~%----------------~%~
                   File: ~x0~%  Testcase: ~x1~%  Should "
                path
                (leotest-testcase->item (leotest-testcase-exec-outcome->testcase testcase-outcome)))
            (if passp
                (cw "have executed (according to the expectation),~%  but the ACL2 Leo executor did not execute it.~%")
              (cw "have failed executing (according to the expectation),~%  but the ACL2 Leo executor accepted it.~%")))))

(define report-failed-exec-leotests-for-testcase-outcomes ((path stringp)
                                                           (passp booleanp)
                                                           (testcase-outcomes leotest-testcase-exec-outcome-listp))
  (if (endp testcase-outcomes)
      nil
    (b* ((- (report-failed-exec-leotests-for-testcase-outcome path passp (first testcase-outcomes))))
      (report-failed-exec-leotests-for-testcase-outcomes path passp (rest testcase-outcomes)))))

(define report-failed-exec-leotests-for-file-outcome ((file-outcome leotest-file-exec-outcomesp))
  (b* (((leotest-file-exec-outcomes ltpo) file-outcome))
    (report-failed-exec-leotests-for-testcase-outcomes
     (leotest-file->path ltpo.file-of-tests)
     (leotest-file->passp ltpo.file-of-tests)
     ltpo.outcomes)))

(define report-failed-exec-leotests ((file-outcomes leotest-file-exec-outcomes-listp))
  (if (endp file-outcomes)
      nil
    (b* ((- (report-failed-exec-leotests-for-file-outcome (first file-outcomes))))
      (report-failed-exec-leotests (rest file-outcomes)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top reporting function

(define report-exec-leotests ((test-suite-outcome leotest-suite-exec-outcomesp))
  (b* ((- (cw "~%Results of running ACL2 Leo compiler+executor on leo/tests/ .leo files.~%"))
       (- (cw "See leo-acl2/tests/exec-leotests.lisp for the current limitations.~%"))
       ((leotest-suite-exec-outcomes out) test-suite-outcome)
       (num-files (len out.outcomes))
       (- (cw "~%~x0 test files were found.~%" num-files))
       (- (cw "Running the tests took ~x0 seconds.~%" out.elapsed-time))
       ((mv p f s) (count-pass/fail/skip-tests-files--exec out.outcomes))
       (- (cw "~%There were ~x0 test cases.~%" (+ p f s)))
       (- (cw "  ~x0 failed~%" f))
       (- (cw "  ~x0 passed~%" p))
       (- (cw "  ~x0 skipped (should have been filtered out before we got here)~%" s))
       ((when (> f 0))
        (cw "~%Failed tests listing:~%")
        (report-failed-exec-leotests out.outcomes)))
    nil))
