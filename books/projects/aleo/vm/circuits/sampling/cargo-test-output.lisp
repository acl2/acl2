; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains a utility to convert a cargo test output file
; containing SnarkVM R1CS samples
; to a file containing ACL2 definitions, one for each test.

; At first this generates files in the format such as:
;   aleo-acl2/circuits/samples/field-message-json-auto.lisp
; Later we will include the additional processing of
;   aleo::json-message-group-string-to-constraints
; so we don't have to do that as a separate step.

; Example.
; Run something like (change "your-homedir", "path-to", and the destination file as appropriate):
;
;   /your-homedir/.cargo/bin/cargo test --test integers integers --no-fail-fast --manifest-path /home/batman/snarkVM/circuit/Cargo.toml -- --format=json -Z unstable-options --show-output > /path-to/aleo-acl2/circuits/samples/raw/u64-2023-03-09.txt
;
; Then run this tool:
;
;   (include-book "top")
;   (raw-test-results-file-to-sample-file "~/aleo-acl2/circuits/samples/raw/field-2023-03-14.txt" "~/aleo-acl2/circuits/samples/field-message-json-auto.lisp" state)
;
; Previous example, just running the first part of the tool:
;   (aleo::cargo-test-output-file-to-gadget-json-message-strings "/path-to/aleo-acl2/circuits/samples/raw/u64-2023-03-13.txt" state)

; Other future possibilities: make versions that return PFCS value or FTY version of R1CS

;;;;;;;;;;;;;;;;;;;;

; The top-level JSON structure we call a JSON message group, which contains
; one JSON message entry for each constraint,
; and for each entry, the string value of "message" must be parsed to get the
; constraint.

; This structure differs from the previous structure parsed by
; "gadget-json-to-r1cs-defagg.lisp" in that
; 1. it does does not have the "num_constants", etc. fields --- each message
; string contains just a single constraint;
; 2. there are two levels of parsing JSON from strings here: the outer JSON
;    and then the per-constraint parsing from message strings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Currently only used for the things it includes, and main content will be
; needed later.
(include-book "gadget-json-message-to-r1cs-defagg")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/io/read-file-lines" :dir :system)

(include-book "js-string-to-acl2-string")

(local (include-book "kestrel/utilities/io/output-theory" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The test output should be a single line from the output from "cargo test .."
; If the line
;   does not start with a "{"
;   or the JSON does not parse
;   or the parsed JSON is not of the correct form
;      { "type": "test", "name": "integers::add", "event": "ok", "stdout": "..." }
; then the line is ignored (okp is NIL; name is an error message string with
;     errstring-prefix prepended, and stdout is "").
; If the line is of the correct form, the "name" is turned into a lisp symbol
; and a form of the sort you can see in samples/field-message-json.lisp
;

(define cargo-test-string-to-gadget-json-message-string ((test-output-string stringp)
                                                         (errstring-prefix stringp))
  :returns (mv (okp booleanp) (name stringp) (stdout stringp))
  (b* (((unless (and (stringp test-output-string)
                     (> (length test-output-string) 0)
                     (equal (acl2::char test-output-string 0) #\{)))
        (mv nil (concatenate 'string errstring-prefix "string doesn't look like JSON: " test-output-string) ""))
       ((mv erp json-sexp) (acl2::parse-string-as-json test-output-string))
       ((when erp)
        (mv nil (concatenate 'string errstring-prefix "string started with '{' but JSON failed to parse: " test-output-string) ""))
       ((mv erp json-fty-value)
        (json::parsed-to-value json-sexp))
       ((when erp)
        (mv nil (concatenate 'string errstring-prefix "can't put ACL2 JSON into FTY form") ""))
       ((unless (json::valuep json-fty-value))
        (mv nil (concatenate 'string errstring-prefix "unexpected value returned by json::parsed-to-value") ""))
       ; Right now there are a couple of JSON forms observed that we discard:
       ;   discarded form 1. { "type": "suite", ...}
       ;   discarded form 2. { "type": "test", "event": "started", ...}
       ((json::pattern (:object (:member "type" (:string "test"))
                                (:member "name" (:string raw-test-name))
                                (:member "event" (:string "ok"))
                                (:member "stdout" (:string stdout))))
        json-fty-value)
       ((unless (and json::match?
                     (stringp raw-test-name)
                     (stringp stdout)))
        (mv nil (concatenate 'string errstring-prefix "This form was not a test output: " test-output-string) "")))
    ;; strip out "//" comment, if any, and convert \n to newline.
    (mv t raw-test-name (acl2::js-stdout-string-to-acl2-string stdout))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cargo-test-result
  ((name stringp)
   (output stringp)))

(fty::deflist cargo-test-results
  :elt-type cargo-test-result
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cargo-test-strings-to-gadget-json-message-strings-aux ((test-output-strings string-listp)
                                                                 (next-line-number natp))
    :returns (mv (test-results cargo-test-results-p) (errstrings string-listp))
    (b* (((when (endp test-output-strings))
          (mv nil nil))
         ((mv okp name stdout)
          (cargo-test-string-to-gadget-json-message-string
           (car test-output-strings)
           (concatenate 'string (str::int-to-dec-string next-line-number) ": ")))
         ((mv results errstrs)
          (cargo-test-strings-to-gadget-json-message-strings-aux
           (cdr test-output-strings)
           (+ 1 next-line-number))))
      (if okp
          (mv (cons (make-cargo-test-result :name name :output stdout) results)
              errstrs)
        (mv results (cons name errstrs)))))

; Multi-string version of above that uses the line number as errstring prefix,
; and returns two lists, one from successfully parsed top-level forms and one with line-numbered error messages.
; The first list contains (cons name stdout) forms, where stdout is from the snarkVM test.
(define cargo-test-strings-to-gadget-json-message-strings ((test-output-strings string-listp))
  :returns (mv (test-results cargo-test-results-p) (errstrings string-listp))
  (cargo-test-strings-to-gadget-json-message-strings-aux  test-output-strings 1))

; We don't care if there are newlines at the end of each string, so just use
; the simplest API function, read-file-lines
(define cargo-test-output-file-to-gadget-json-message-strings ((filename stringp) state)
  ; added erp just so we would not have an "error triple", which is bad interactively
  :stobjs state
  :returns (mv (erp booleanp) (ret-test-results cargo-test-results-p) (ret-errstrings string-listp) state)
  (b* (((mv data state)
        (acl2::read-file-lines filename state))
       ((when (stringp data)) ; read-file-lines got an error
        (mv t nil (list (concatenate 'string "read-file-lines error: " data)) state))
       ((unless (string-listp data))
        (mv t nil (list "unexpected return value from read-file-lines") state))
       ((mv test-results errstrings)
        (cargo-test-strings-to-gadget-json-message-strings data)))
    (mv nil test-results errstrings state))
  ///
  (defthm state-p-of-cargo-test-output-file-to-gadget-json-message-strings
    (mv-let (e rtr re ret-state)
        (cargo-test-output-file-to-gadget-json-message-strings fn state)
      (declare (ignorable e rtr re))
      (implies (state-p state)
               (state-p ret-state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Take a cargo-test-result (a test name and a test output string (in JSON
; "message group" form) and generate a defconst similar to what we see in
; samples/field-message-json.lisp, writing it to the given character output
; channel, so we can capture the samples in loadable files.

(define write-defconst-for-cargo-test-result ((test-result cargo-test-result-p)
                                              (co symbolp)
                                              state)
  :guard (open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* (((cargo-test-result r) test-result)
       ;; we assume r.name does not contain vertical bar "|"
       (printname (concatenate 'string "|*" r.name "*|"))
       (the-output r.output)
       ;; Now we use princ$ instead of fmt! to do the printing.  Reasons:
       ;; (1) I don't see a FMT! directive that is
       ;; analogous to the Common Lisp format directive ~a
       ;; (2) princ$ is in logic mode.
       (nl acl2::*newline-string*)
       (state (princ$ nl co state))
       (state (princ$ "(defconst " co state))
       (state (princ$ printname co state))
       (state (princ$ nl co state))
       (state (princ$ "#{\"\"\"" co state))
       (state (princ$ nl co state))
       (state (princ$ the-output co state))
       (state (princ$ nl co state))
       (state (princ$ "\"\"\"})" co state))
       (state (princ$ nl co state)))
    state)
  ///
  (defthm state-p-of-write-defconst-for-cargo-test-result
    (let ((ret (write-defconst-for-cargo-test-result tr channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-write-defconst-for-cargo-test-result
    (let ((ret (write-defconst-for-cargo-test-result tr channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-sample-file-header-top ()
  :returns (header-top stringp)
"; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; Authors: Alessandro Coglio (acoglio on GitHub)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package \"ALEO\")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
")

(define write-r1cs-sample-file-header-where-from ((cargo-test-output-filename stringp)
                                                  (defconst-filename stringp)
                                                  (co symbolp)
                                                  state)
  :guard (acl2::open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* ((state (princ$ "
; These JSON forms came from running
;   (include-book \"circuits/cargo-test-output\")
;   (raw-test-results-file-to-sample-file
;      " co state))
       (state (prin1$ cargo-test-output-filename
                      co state))
       (state (princ$ "
;      " co state))
       (state (prin1$ defconst-filename
                      co state))
       (state (princ$ "
;      state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
"
                      co state)))
    state)
  ///
  (defthm state-p-of-write-r1cs-sample-file-header-where-from
    (let ((ret (write-r1cs-sample-file-header-where-from f1 f2 channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-write-r1cs-sample-file-header-where-from
    (let ((ret (write-r1cs-sample-file-header-where-from f1 f2 channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

(define write-r1cs-sample-file-header ((cargo-test-output-filename stringp)
                                       (defconst-filename stringp)
                                       (co symbolp)
                                       state)
  :guard (acl2::open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* ((state
        (princ$ (r1cs-sample-file-header-top)
                co state))
       (state
        (write-r1cs-sample-file-header-where-from
         cargo-test-output-filename
         defconst-filename
         co
         state)))
    state)
  ///
  (defthm state-p-of-write-r1cs-sample-file-header
    (let ((ret (write-r1cs-sample-file-header f1 f2 channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-write-r1cs-sample-file-header
    (let ((ret (write-r1cs-sample-file-header f1 f2 channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

(define write-defconsts-for-cargo-test-results ((test-results cargo-test-results-p)
                                               (co symbolp)
                                               state)
  :guard (acl2::open-output-channel-p co :character state)
  :stobjs state
  :returns state

  (if (endp test-results)
      state
    (b* ((state (write-defconst-for-cargo-test-result (car test-results)
                                                      co
                                                      state)))
      (write-defconsts-for-cargo-test-results (cdr test-results) co state)))
  ///
  (defthm state-p-of-write-defconsts-for-cargo-test-results
    (let ((ret (write-defconsts-for-cargo-test-results trs channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-write-defconsts-for-cargo-test-results
    (let ((ret (write-defconsts-for-cargo-test-results trs channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Take a list of cargo-test-result and
; and write a file containing defconsts for them.

(define write-sample-file ((raw-file-name-to-record-in-header stringp)
                           (test-results cargo-test-results-p)
                           (filename stringp)
                           state)
  :stobjs state
  :returns state
  (mv-let (co state)
      (open-output-channel filename :character state)
    (if (not (open-output-channel-p co :character state))
        state
      (b* ((nl acl2::*newline-string*)
           (state (write-r1cs-sample-file-header raw-file-name-to-record-in-header
                                                 filename
                                                 co
                                                 state))
           (state (princ$ nl co state))
           (state (write-defconsts-for-cargo-test-results
                   test-results co state)))
        (close-output-channel co state))))
  ///
  (defthm state-p-of-write-sample-file
    (let ((ret (write-sample-file f1 trs f2 state)))
      (implies (state-p state)
               (state-p ret)))))

(define raw-test-results-file-to-sample-file ((raw-file stringp)
                                              (defconsts-file stringp)
                                              state)
  :stobjs state
  :returns state
  (b* (((mv ?erp results ?errstrings state)
      ;; TODO: report erp and errstrings
        (cargo-test-output-file-to-gadget-json-message-strings raw-file state)))
    (write-sample-file raw-file
                       results
                       defconsts-file
                       state))
  ///
  (defthm state-p-of-raw-test-results-file-to-sample-file
    (let ((ret (raw-test-results-file-to-sample-file f1 f2 state)))
      (implies (state-p state)
               (state-p ret)))))

;; Example call:
;; (raw-test-results-file-to-sample-file "~/aleo-acl2/circuits/samples/raw/field-2023-03-14.txt" "~/aleo-acl2/circuits/samples/field-message-json-auto.lisp" state)
