; Java Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "factorial")
(include-book "fibonacci")
(include-book "abnf")

(include-book "std/io/read-file-characters" :dir :system)
(include-book "std/strings/decimal" :dir :system)

; (depends-on "../../../../projects/abnf/notation/core-rules.abnf")
; (depends-on "../../../../projects/abnf/notation/concrete-syntax-rules.abnf")
; (depends-on "../../../../projects/abnf/examples/uri.abnf")
; (depends-on "../../../../projects/abnf/examples/http.abnf")
; (depends-on "../../../../projects/abnf/examples/imf.abnf")
; (depends-on "../../../../projects/abnf/examples/smtp.abnf")
; (depends-on "../../../../projects/abnf/examples/imap.abnf")
; (depends-on "../../../c/language/grammar.abnf")
; (depends-on "../../../java/language/lexical-grammar.abnf")
; (depends-on "../../../java/language/syntactic-grammar.abnf")
; (depends-on "../../../json/grammar.abnf")
; (depends-on "../../../yul/language/grammar.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file collects some of the ATJ tests in this directory
; and provides utilities to measure their execution times in the ACL2 shell.
; Some of these utilities should be moved to more general libraries,
; perhaps after making some of them a little more general.
; These times are useful to compare with execution in Java.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Since the times measured by ACL2 via READ-RUN-TIME are rational numbers,
; the following utilities serve
; to calculate minimum, maximum, and average of a sequence of time measurements,
; as well as to format these time measurements in a readable way.

; Minimum of a non-empty list of rationals.
(define list-min ((list rational-listp))
  :guard (consp list)
  (if (endp (cdr list))
      (car list)
    (min (car list) (list-min (cdr list)))))

; Maximum of a non-empty list of rationals.
(define list-max ((list rational-listp))
  :guard (consp list)
  (if (endp (cdr list))
      (car list)
    (max (car list) (list-max (cdr list)))))

; Sum of a list of rationals.
(define list-sum ((list rational-listp))
  (if (endp list)
      0
    (+ (car list) (list-sum (cdr list)))))

; Average of a non-empty list of rationals.
(define list-avg ((list rational-listp))
  :guard (consp list)
  (/ (list-sum list) (len list)))

; Format a rational time in seconds, rounding it to the millisecond.
(define format-time ((seconds rationalp))
  :verify-guards nil
  (b* ((milliseconds (* seconds 1000))
       (milliseconds-int (round milliseconds 1))
       (seconds-int (floor milliseconds-int 1000))
       (seconds-frac (mod milliseconds-int 1000))
       (frac-str (cond ((< seconds-frac 10)
                        (str::cat "00" (str::nat-to-dec-string seconds-frac)))
                       ((< seconds-frac 100)
                        (str::cat "0" (str::nat-to-dec-string seconds-frac)))
                       (t (str::nat-to-dec-string seconds-frac)))))
    (msg "~x0.~s1" seconds-int frac-str)))

; Obtain the content of the specified file, as a list of natural numbers.
(define get-input-from-file ((filename stringp) state)
  :returns (mv nats state)
  :mode :program
  (b* ((path (string-append (cbd) filename))
       ((mv chars state) (read-file-characters path state))
       (nats (chars=>nats chars)))
    (mv nats state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities to measure times for the factorial function.

; Make M calls of the factorial function on INPUT,
; and return the list of results.
; Each time measurement applies to M calls:
; set M to 1 to measure the time of single calls,
; or to larger values when the calls are fast
; and longer measurement times are desired.
(define run-fact-calls ((input natp) (m natp) gcheck)
  :returns (results)
  (b* (((when (zp m)) nil)
       (result (with-guard-checking gcheck (fact input)))
       (results (run-fact-calls input (1- m) gcheck)))
    (cons result results)))

; Make N * M calls of the factorial function on INPUT,
; printing the time taken by each of the N sequences of M calls
; and returning the list of the times for all the sequences of M calls.
; The GCHECK argument provides the guard checking settings.
(define run-fact-test ((input natp) (n natp) (m natp) gcheck state)
  :returns (mv times state)
  :verify-guards nil
  (b* (((when (zp n)) (mv nil state))
       ;; record start time:
       ((mv start state) (read-run-time state))
       ;; execute the M calls:
       (results (run-fact-calls input m gcheck))
       ;; record end time:
       ((mv end state) (read-run-time state))
       ;; prevent unwanted Lisp compiler optimizations:
       ((when (endp results)) (mv nil state)) ; never happens
       ;; print time for the M calls:
       (time (- end start))
       (- (cw "  ~@0~%" (format-time time)))
       ((mv times state) (run-fact-test input (1- n) m gcheck state)))
    (mv (cons time times) state)))

; Make N * M calls of the factorial function on each element of INPUTS,
; printing the time taken by each of the N sequences of M calls call
; and printing minimum, maximum, and average times for each input.
; The GCHECK argument provides the guard checking settings.
(define run-fact-tests ((inputs nat-listp) (n natp) (m natp) gcheck state)
  :returns state
  :verify-guards nil
  (b* (((when (endp inputs)) state)
       (input (car inputs))
       (- (cw "~%Times (in seconds) to run factorial on ~x0:~%" input))
       ((mv times state) (run-fact-test input n m gcheck state))
       (- (cw "Minimum: ~@0~%" (format-time (list-min times))))
       (- (cw "Average: ~@0~%" (format-time (list-avg times))))
       (- (cw "Maximum: ~@0~%" (format-time (list-max times)))))
    (run-fact-tests (cdr inputs) n m gcheck state)))

; Making a call like the following in the ACL2 shell
; runs the factorial function on each input for the specified number of times
; and prints the resulting times.
#|
(run-fact-tests '(1000 5000 10000 50000 100000) 10 1 t state)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities to measure times for the Fibonacci function.

; Make M calls of the Fibonacci function on INPUT,
; and return the list of results.
; Each time measurement applies to M calls:
; set M to 1 to measure the time of single calls,
; or to larger values when the calls are fast
; and longer measurement times are desired.
(define run-fib-calls ((input natp) (m natp) gcheck)
  :returns (results)
  (b* (((when (zp m)) nil)
       (result (with-guard-checking gcheck (fib input)))
       (results (run-fib-calls input (1- m) gcheck)))
    (cons result results)))

; Make N * M calls of the Fibonacci function on INPUT,
; printing the time taken by each of the N sequences of M calls
; and returning the list of the times for all the calls.
; The GCHECK argument provides the guard checking settings.
(define run-fib-test ((input natp) (n natp) (m natp) gcheck state)
  :returns (mv times state)
  :verify-guards nil
  (b* (((when (zp n)) (mv nil state))
       ;; record start time:
       ((mv start state) (read-run-time state))
       ;; execute the M calls:
       (results (run-fib-calls input m gcheck))
       ;; record end time:
       ((mv end state) (read-run-time state))
       ;; prevent unwanted Lisp compiler optimizations:
       ((when (endp results)) (mv nil state)) ; never happens
       ;; print time for the M calls:
       (time (- end start))
       (- (cw "  ~@0~%" (format-time time)))
       ((mv times state) (run-fib-test input (1- n) m gcheck state)))
    (mv (cons time times) state)))

; Make N calls of the Fibonacci function on each element of INPUTS,
; printing the time taken by each of the N sequences of M calls call
; and printing minimum, maximum, and average times for each input.
; The GCHECK argument provides the guard checking settings.
(define run-fib-tests ((inputs nat-listp) (n natp) (m natp) gcheck state)
  :returns state
  :verify-guards nil
  (b* (((when (endp inputs)) state)
       (input (car inputs))
       (- (cw "~%Times (in seconds) to run Fibonacci on ~x0:~%" input))
       ((mv times state) (run-fib-test input n m gcheck state))
       (- (cw "Minimum: ~@0~%" (format-time (list-min times))))
       (- (cw "Average: ~@0~%" (format-time (list-avg times))))
       (- (cw "Maximum: ~@0~%" (format-time (list-max times)))))
    (run-fib-tests (cdr inputs) n m gcheck state)))

; Making a call like the following in the ACL2 shell
; runs the Fibonacci function on each input for the specified number of times
; and prints the resulting times.
#|
(run-fib-tests '(10 20 30 40) 10 1 t state)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities to measure times for the ABNF grammar parser.

; Make M calls of the ABNF parser function on INPUT,
; and return the list of results.
; Each time measurement applies to M calls:
; set M to 1 to measure the time of single calls,
; or to larger values when the calls are fast
; and longer measurement times are desired.
(define run-abnf-calls ((input nat-listp) (m natp) gcheck)
  :returns (results)
  (b* (((when (zp m)) nil)
       (result (with-guard-checking gcheck (abnf::parse-grammar input)))
       (result (consp result)) ; reduce memory to avoid garbage collection
       (results (run-abnf-calls input (1- m) gcheck)))
    (cons result results)))

; Make N * M calls of the ABNF parser on INPUT,
; printing the time taken by each of the N seequence of M calls
; and returning the list of the times for all the calls.
; The GCHECK argument provides the guard checking settings.
(define run-abnf-test ((input nat-listp) (n natp) (m natp) gcheck state)
  :returns (mv times state)
  :verify-guards nil
  (b* (((when (zp n)) (mv nil state))
       ;; record start time:
       ((mv start state) (read-run-time state))
       ;; execute the M calls:
       (results (run-abnf-calls input m gcheck))
       ;; record end time:
       ((mv end state) (read-run-time state))
       ;; prevent unwanted Lisp compiler optimizations:
       ((when (endp results)) (mv nil state)) ; never happens
       ;; print time for the M calls:
       (time (- end start))
       (- (cw "  ~@0~%" (format-time time)))
       ((mv times state) (run-abnf-test input (1- n) m gcheck state)))
    (mv (cons time times) state)))

; Make N * M calls of the ABNF parser on each element of INPUTS,
; printing the time taken by each of the N seequence of M calls
; and printing minimum, maximum, and average times for each input.
; The GRAMMARS argument is just used for printing.
; The GCHECK argument provides the guard checking settings.
(define run-abnf-tests
  ((inputs true-listp) (grammars symbol-listp) (n natp) (m natp) gcheck state)
  :returns state
  :verify-guards nil
  (b* (((when (endp inputs)) state)
       (input (car inputs))
       (- (cw "~%Times (in seconds) to run the parser ~
               on the ~x0 grammar:~%" (car grammars)))
       ((mv times state) (run-abnf-test input n m gcheck state))
       (- (cw "Minimum: ~@0~%" (format-time (list-min times))))
       (- (cw "Average: ~@0~%" (format-time (list-avg times))))
       (- (cw "Maximum: ~@0~%" (format-time (list-max times)))))
    (run-abnf-tests (cdr inputs) (cdr grammars) n m gcheck state)))

; The input to the ABNF grammar parser must be a list of natural numbers,
; read from some ABNF grammar file.
; These events are using the program-mode function READ-FILE-CHARACTERS,
; via the (necessarily program-mode) function GET-INPUT-FROM-FILE above.
; In order to run the ABNF grammar parser in logic mode,
; the contents of the files are stored in the following constants,
; which can then be directly fed into RUN-ABNF-TESTS.
; Add more constants like these if you want to test the parser on other files.
(progn
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/notation/core-rules.abnf" state)
     (value `(defconst *abnf-core* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/notation/concrete-syntax-rules.abnf" state)
     (value `(defconst *abnf-syntax* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/examples/uri.abnf" state)
     (value `(defconst *uri* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/examples/http.abnf" state)
     (value `(defconst *http* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/examples/imf.abnf" state)
     (value `(defconst *imf* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/examples/smtp.abnf" state)
     (value `(defconst *smtp* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../../projects/abnf/examples/imap.abnf" state)
     (value `(defconst *imap* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../c/language/grammar.abnf" state)
     (value `(defconst *c* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../java/language/lexical-grammar.abnf" state)
     (value `(defconst *java-lexical* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../java/language/syntactic-grammar.abnf" state)
     (value `(defconst *java-syntactic* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../json/grammar.abnf" state)
     (value `(defconst *json* ',nats))))
  (make-event
   (mv-let (nats state)
     (get-input-from-file "../../../yul/language/grammar.abnf" state)
     (value `(defconst *yul* ',nats)))))

; Making a call like the following in the ACL2 shell
; runs the ABNF grammar parser on each input for the specified number of times
; and prints the resulting times.
; Note that the second argument must suitably "match" the first one
; (so that the printed messages make sense).
#|
(run-abnf-tests (list *abnf-core*
                      *abnf-syntax*
                      *uri*
                      *http*
                      *imf*
                      *smtp*
                      *imap*
                      *c*
                      *java-lexical*
                      *java-syntactic*
                      *json*
                      *yul*)
                '(abnf-core
                  abnf-syntax
                  uri
                  http
                  imf
                  smtp
                  imap
                  c
                  java-lexical
                  java-syntactic
                  json
                  yul)
                10
                1
                t
                state)
|#
