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

(include-book "parser-for-leo-test-files")

(include-book "../definition/parser-interface")

; This next book is solely for the valid address check.
; We may want to refactor the testing code so that
; this book is not dependent on the abstractor, or possibly
; just to make a separate micro-abstractor for testing addresses.
(include-book "../definition/syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we introduce code to run the ACL2 Leo parser over the leo test files.
; First we define data types to capture the test outcomes.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcome of parsing a single leo test case.
; Does not store the category (ie. namespace) or passp (expectation)
; since those are file-level attributes.

(fty::defprod leotest-testcase-parse-outcome
  ((testcase leotest-testcasep) ; this duplicates the testcase, for convenience
   (skip? bool) ; if this test is not applicable for a parse tests---
                ; for example, a namespace: Compiler expectation: Fail test
                ; could be expected to fail due to type checking, not due to parsing,
                ; so we should really skip it for parsing.
   (ok? bool) ; T means the test did the right thing.
              ; If it is a must-fail test, T means the parse failed.
   ;; consider adding optional time and space measures
  )
  :pred leotest-testcase-parse-outcomep)

(fty::deflist leotest-testcase-parse-outcome-list
  :elt-type leotest-testcase-parse-outcome
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-testcase-parse-outcome-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcomes of parsing zero or more leotests in a leotest file.

(fty::defprod leotest-file-parse-outcomes
  (;; Now links to the file for file-level info such as
   ;; file name, category, and passp,
   ;; but we could copy those things to here and skip the link.
   (file-of-tests leotest-filep)
   (outcomes leotest-testcase-parse-outcome-list)
   ;; consider adding optional time and space measures
   ;; consider adding a timestamp per file here
  )
  :pred leotest-file-parse-outcomesp)

(fty::deflist leotest-file-parse-outcomes-list
  :elt-type leotest-file-parse-outcomes
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-file-parse-outcomes-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype for the outcomes of running the tests in a list of files.

(fty::defprod leotest-suite-parse-outcomes
  (;; consider adding leo version and commit
   ;; consider adding leo-acl2 commit, cl version
   (start-time string)
   (end-time string)
   (elapsed-time integerp)
   (outcomes leotest-file-parse-outcomes-listp))
  :pred leotest-suite-parse-outcomesp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check for invalid addresses in multi-token tests

(define free-of-invalid-addresses? ((tokens abnf::tree-listp))
  :returns (y/n booleanp)
  (if (endp tokens)
      t
    (b* ((lit (abs-atomic-literal (first tokens)))
         ((when (and (literalp lit)
                     (literal-case lit :address)
                     (addressp (literal-address->get lit))
                     (not (address-valid-p (literal-address->get lit)))))
          nil))
      (free-of-invalid-addresses? (rest tokens)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; multi-token tests

; `namespace: Token` in the leotest file header
; does not mean the same thing as a token in the abnf grammar.
; Rather, it means each line is "tokenized" into N tokens.

; For expectation: Pass, the test framework expectation file
; will have the expected list of tokens in it.
; For expectation: Fail, it is expected that there is some
; problem tokenizing the line, but it doesn't say anything about
; how many tokens were successfully found before the failure.
;
; Since the line can have whitespace separating tokens,
; and since that whitespace is not directly captured in the
; `.out` file (*), we don't want to require the ACL2 Leo parser
; have the same fringe (surface syntax) as the original text.
;
; (*) although there is span information, so the
;     parts between the span info is the whitespace

; Because of this, we define an interface function
; for multiple tokens.  We are not requiring that the
; tokens form a syntactic whole.  The purpose is to test the
; Rust Leo lexer/tokenizer.  This roughly corresponds to our
; lexing and tokenizing.

; Also we check that there are no "invalid" addresses,
; in the sense of addresses that parsed but have an invalid
; checksum according to the bech32 / bech32m rules.
; The reason we do that here is to closer match the
; Leo parser, which gets an error if an invalid address
; is lexed.

(define one-or-more-tokens-parse? ((item-string stringp))
  (b* ((lexemes (lexemize-leo-from-string item-string))
       ((when (reserrp lexemes)) nil)
       (lexemes (abnf::tree-list-fix lexemes))
       (tokens (filter-and-lower-tokens lexemes))
       ((when (reserrp tokens))
        nil))
    (and (free-of-invalid-addresses? tokens)
         (< 0 (len tokens)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a single test.

(define run-parse-leotest ((testcase leotest-testcasep)
                           (cat leotest-categoryp)
                           (should-parse? booleanp))
  :returns (test-outcome leotest-testcase-parse-outcomep)
  ;; given a string from a single testcase from a leotest file,
  ;; returns a leotest-testcase-parse-outcome.
  ;; Note that parsing ignores the input path and contents
  ;; that are in the testcase,
  (b* ((item-string (leotest-testcase->item testcase))
       (outcome
        (if should-parse?
            ;; as with the the unit tests,
            ;; for a test that should parse,
            ;; use the more restrictive predicate file-parses-same-fringe?
            (leotest-category-case
             cat
             :parse-token (one-or-more-tokens-parse? item-string)
             :parse-expression (expression-parses-same-fringe? item-string)
             :parse-statement (statement-parses-same-fringe? item-string)
; namespace: Import tests have been moved out of leo for now.
;             :import (raise "running Import tests not yet supported")
             ;; for the others, :parse-file and :compile and :serialize,
             ;; we parse the string as a leo-early::file
             :otherwise (and (file-parses-same-fringe? item-string)
                             ;; Special check for valid addresses.
                             ;; For "expectation: Pass" tests, all addresses
                             ;; should be valid.
                             ;; Since the ACL2 Leo parser doesn't check that
                             ;; (it is checked at type-checking time)
                             ;; we do an extra check here to mimic
                             ;; the Rust Leo parser.
                             ;; See also the comment below for the
                             ;; "expectation: Fail" case.
                             (b* ((lexemes (lexemize-leo-from-string item-string))
                                  ((when (reserrp lexemes)) nil)
                                  (tokens (filter-and-lower-tokens lexemes))
                                  ((when (reserrp tokens)) nil))
                               (free-of-invalid-addresses? tokens))))
          ;; for a test that should not parse ("expectation: Fail"),
          ;; use the less restrictive predicate file-parses?
          (leotest-category-case
           cat
           :parse-token (not (one-or-more-tokens-parse? item-string))
           :parse-expression (not (expression-parses? item-string))
           :parse-statement (not (statement-parses? item-string))
           :compile nil ; we skip these
                        ; namespace: Import tests have been moved out of leo for now.
                        ;           :import (raise "running Import tests not yet supported")
           ;; for the others, :parse-file and :compile and :serialize,
           ;; we parse the string as a leo-early::file
           :otherwise (or (not (file-parses? item-string))
                          ;; Another way we could have "expectation: Fail" on
                          ;; the Leo test case is when the file parses but there
                          ;; is an invalid address.
                          ;; This is a difference between the ACL2 Leo parser
                          ;; and the Rust Leo parser.  The Rust Leo parser
                          ;; gets an error if there is an invalid address.
                          ;; The ACL2 Leo parser doesn't do syntax abstraction,
                          ;; or address validity checking.
                          ;; To make these tests more aligned with the Leo parser,
                          ;; if there are any invalid addresses, we mark this
                          ;; "namespace: Parse; expectation: Fail" test a success.
                          ;; [ Note, there is an interface function for ASTs
                          ;;   (ast-addresses-valid? ..) but because the ACL2 Leo
                          ;;   parser doesn't do abstraction we don't have the AST.
                          ;;   Instead, we must look for address tokens in the
                          ;;   tokenized form. ]
                          (b* (;; Since at this point we know the file parses,
                               ;; we will not have any reserrp from lexing
                               ;; or tokenizing, but for safety and type safety
                               ;; we allow such reserrps to call this
                               ;; "expectation: Fail" test a success
                               (lexemes (lexemize-leo-from-string item-string))
                               ((when (reserrp lexemes)) t)
                               (tokens (filter-and-lower-tokens lexemes))
                               ((when (reserrp tokens)) t))
                            (not (free-of-invalid-addresses? tokens))))))))
    (make-leotest-testcase-parse-outcome
     :testcase testcase
     ;; For :compile, the param "should-parse?", since it comes from expectation:,
     ;; really means "should-compile?".  This doesn't tell us whether
     ;; it should parse, so we skip it.
     :skip? (and (leotest-category-case cat :compile) (not should-parse?))
     :ok? outcome)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Unit tests for run-parse-leotest, one of each kind of input

(assert-event (run-parse-leotest (make-leotest-testcase :item "'\\u{0}'")
                                 (make-leotest-category-parse-token)
                                 t))
(assert-event (run-parse-leotest (make-leotest-testcase :item "'\\u{}'")
                                 (make-leotest-category-parse-token)
                                 nil))
(assert-event (run-parse-leotest (make-leotest-testcase :item "/**/3+5 ")
                                 (make-leotest-category-parse-expression)
                                 t))
(assert-event (run-parse-leotest (make-leotest-testcase :item "/**/3+5+ ")
                                 (make-leotest-category-parse-expression)
                                 nil))
(assert-event (run-parse-leotest (make-leotest-testcase :item "return;")
                                 (make-leotest-category-parse-statement)
                                 t))
(assert-event (run-parse-leotest (make-leotest-testcase :item "return")
                                 (make-leotest-category-parse-statement)
                                 nil))
(assert-event (run-parse-leotest (make-leotest-testcase
                                  :item
                                  "function main(a:u8)->u8 {return 3u8;}")
                                 (make-leotest-category-parse-file)
                                 t))
(assert-event (run-parse-leotest (make-leotest-testcase
                                  :item
                                  "function main(a:u8)->u8 {return 3;}")
                                 (make-leotest-category-parse-file)
                                 nil))
(assert-event (run-parse-leotest (make-leotest-testcase
                                  :item
                                  "//
function main(a:u8)->u8 {return 3u8;}// another comment")
                                 (make-leotest-category-compile)
                                 t))
(assert-event (run-parse-leotest (make-leotest-testcase
                                  :item
                                  "function main(a:u8)->u8 {return 3u8;}/* * /")
                                 (make-leotest-category-compile)
                                 nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a list of similar tests

(define run-parse-leotests ((testcases leotest-testcase-listp)
                            (cat leotest-categoryp)
                            (should-parse? booleanp))
  :returns (test-outcomes leotest-testcase-parse-outcome-listp)
  (if (endp testcases) nil
    (cons (run-parse-leotest (car testcases) cat should-parse?)
          (run-parse-leotests (cdr testcases) cat should-parse?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run the tests defined in a leotest file

(define run-parse-leotest-file ((ltfile leotest-filep))
  :returns (file-outcomes leotest-file-parse-outcomesp)
  (b* (((leotest-file ltf) ltfile) ;creates ltf.path, etc.
       (outcomes (run-parse-leotests ltf.testcases ltf.category ltf.passp)))
    (make-leotest-file-parse-outcomes
     :file-of-tests ltfile
     :outcomes outcomes)))

; Quick unit test
; (mv-let (ltf state) (leotest-parse-file-at-path "~/leo/tests/parser/expression/binary/add.leo" state) (mv (run-parse-leotest-file ltf) state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Run a list of files of tests

(define run-parse-leotest-files ((files leotest-file-listp))
  :returns (outcomes leotest-file-parse-outcomes-listp)
  (if (endp files) nil
    (cons (run-parse-leotest-file (car files))
          (run-parse-leotest-files (cdr files)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See also tests/parsing-leotests.lisp

; Running a test suite is defined in tests/parse-leotests.lisp
; because it fetches the system date, which requires a trust tag,
; and we are trying to limit trust tags to the leo-acl2/tests/ directory.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Reporting

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Counting the number of passed and failed and skipped items

(define count-pass/fail/skip-tests-items ((outcomes leotest-testcase-parse-outcome-listp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (if (endp outcomes)
      (mv 0 0 0)
    (b* ((skip? (leotest-testcase-parse-outcome->skip? (first outcomes)))
         ((mv p f s) (if skip?
                         (mv 0 0 1)
                       (if (leotest-testcase-parse-outcome->ok? (first outcomes))
                           (mv 1 0 0)
                         (mv 0 1 0))))
         ((mv pn fn sn) (count-pass/fail/skip-tests-items (rest outcomes))))
      (mv (+ p pn) (+ f fn) (+ s sn)))))

(define count-pass/fail/skip-tests-file ((file leotest-file-parse-outcomesp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (count-pass/fail/skip-tests-items
   (leotest-file-parse-outcomes->outcomes file)))

(define count-pass/fail/skip-tests-files ((files leotest-file-parse-outcomes-listp))
  :returns (mv (ret-passes natp) (ret-fails natp) (ret-skips natp))
  (if (endp files)
      (mv 0 0 0)
    (b* (((mv p f s) (count-pass/fail/skip-tests-file (first files)))
         ((mv pn fn sn) (count-pass/fail/skip-tests-files (rest files))))
      (mv (nfix (+ p pn)) (nfix (+ f fn)) (nfix (+ s sn))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List the failed test cases

(define report-failed-leotests-for-testcase-outcome ((path stringp)
                                                     (passp booleanp)
                                                     (testcase-outcome leotest-testcase-parse-outcomep))
  (if (or (leotest-testcase-parse-outcome->ok? testcase-outcome)
          (leotest-testcase-parse-outcome->skip? testcase-outcome))
      nil
    (progn$ (cw "~%File: ~x0~%  Item: ~x1~%  Should " path (leotest-testcase->item (leotest-testcase-parse-outcome->testcase testcase-outcome)))
            (if passp
                (cw "have parsed (according to the expectation),~%  but the ACL2 Leo parser did not parse it.~%")
              (cw "have failed parsing (according to the expectation),~%  but the ACL2 Leo parser accepted it.~%")))))

(define report-failed-leotests-for-testcase-outcomes ((path stringp)
                                                      (passp booleanp)
                                                      (testcase-outcomes leotest-testcase-parse-outcome-listp))
  (if (endp testcase-outcomes)
      nil
    (b* ((- (report-failed-leotests-for-testcase-outcome path
                                                         passp
                                                         (first testcase-outcomes))))
      (report-failed-leotests-for-testcase-outcomes path
                                                    passp
                                                    (rest testcase-outcomes)))))

(define report-failed-leotests-for-file-outcome ((file-outcome leotest-file-parse-outcomesp))
  (b* (((leotest-file-parse-outcomes ltpo) file-outcome))
    (report-failed-leotests-for-testcase-outcomes
     (leotest-file->path ltpo.file-of-tests)
     (leotest-file->passp ltpo.file-of-tests)
     ltpo.outcomes)))

(define report-failed-leotests ((file-outcomes leotest-file-parse-outcomes-listp))
  (if (endp file-outcomes)
      nil
    (b* ((- (report-failed-leotests-for-file-outcome (first file-outcomes))))
      (report-failed-leotests (rest file-outcomes)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Top reporting function

(define report-parse-leotests ((test-suite-outcome leotest-suite-parse-outcomesp))
  (b* ((- (cw "~%Results of running ACL2 Leo parser on leo/tests/ .leo files.~%"))
       (- (cw "See leo-acl2/tests/parse-leotests.lisp for the current limitations.~%"))
       ((leotest-suite-parse-outcomes out) test-suite-outcome)
       (num-files (len out.outcomes))
       (- (cw "~%~x0 test files were found.~%" num-files))
       (- (cw "Running the tests took ~x0 seconds.~%" out.elapsed-time))
       ((mv p f s) (count-pass/fail/skip-tests-files out.outcomes))
       (- (cw "~%There were ~x0 test cases.~%" (+ p f s)))
       (- (cw "  ~x0 failed~%" f))
       (- (cw "  ~x0 passed~%" p))
       (- (cw "  ~x0 skipped (not applicable to parsing)~%" s))
       ((when (> f 0))
        (cw "~%Failed tests listing:~%")
        (report-failed-leotests out.outcomes)))
    nil))
