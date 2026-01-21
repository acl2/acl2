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

(include-book "std/io/read-file-lines-no-newlines" :dir :system) ; for read-file-lines-no-newlines
(include-book "std/io/read-file-characters" :dir :system) ; for read-file-as-string
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/json/parser-output-to-values" :dir :system)
(include-book "kestrel/typed-lists-light/map-char-code" :dir :system)
(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)
(include-book "kestrel/utilities/strings/hexstrings" :dir :system)

(include-book "../json2ast/json-span-removal")
(include-book "../json2ast/json2ast")

(include-book "parsing")

(include-book "../definition/syntax-abstraction")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Temporarily put this file in program mode, due to json2ast.lisp being
;; in program mode.  EM 2021-08-29
(acl2::program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Useful forms:
;;
;; (jsonfile-to-spanfree "~/leo-asts-12/compiler/tests/integers/u8/add.json" state)
;; (jsonfile-to-formal "~/leo-asts-12/compiler/tests/integers/u8/add.json" state)
;;
;; (jsonfile-to-formal-tests "~/leo-asts-12-files.txt" state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Look at the ACL2 version of the JSON AST after removing spans objects/

(define jsonfile-to-spanfree ((filename stringp) state)
  :returns (mv (erp booleanp)
               (spanfree-json json::valuep)
               state)
  (b* (((mv erp j state) (acl2::parse-file-as-json filename state))
       ((when erp) (mv t (json::make-value-null) state))
       ((mv erp tj) (json::parsed-to-value j))
       ((when erp) (mv t (json::make-value-null) state))
       (spanfree-tj (json-remove-spans-in-value tj)))
    (mv erp spanfree-tj state)))


;; Convert JSON AST to ACL2 AST.

(define jsonfile-to-formal ((filename stringp) state)
  :returns (mv (erp booleanp)
               (ret-file file)
               state)
  (b* (((mv erp spanfree-tj state) (jsonfile-to-spanfree filename state))
       ((when erp) (mv t *error-file* state)) ; ignore the error spanfree-tj for now
       ((mv erp ast) (j2f-file spanfree-tj)))
    (mv erp ast state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Versions of above that also returns a sha-256 hash hex string
;; so that you have a way to detect if a file was changed after it was parsed.

;; The sha-256-bytes function on the file's bytes yields the same result as
;; the linux sha256sum command.
;; To see that, do:
;;   (include-book "kestrel/utilities/strings/hexstrings" :dir :system)
;;   (ubyte8s=>hexstring (sha2::sha-256-bytes (map-char-code (read-file-into-character-list <FILENAME> state))))

(define jsonfile-to-spanfree-and-sha256 ((filename stringp) state)
  :returns (mv (erp booleanp)
               (spanfree-json json::valuep)
               (hashstring stringp)
               state)
  (b* (((mv erp j chars state) (acl2::parse-file-as-json-aux filename state))
       ((when erp) (mv t (json::make-value-null) "" state))
       ((mv erp tj) (json::parsed-to-value j))
       ((when erp) (mv t (json::make-value-null) "" state))
       (spanfree-tj (json-remove-spans-in-value tj))
       ((when (> (len chars) sha2::*sha-256-max-message-bytes*))
        (mv t (json::make-value-null) "" state))
       (char-codes (acl2::map-char-code chars))
       (sha256-bytes (sha2::sha-256-bytes char-codes))
       (sha256-hexstring (acl2::ubyte8s=>hexstring sha256-bytes)))
    ;; downcase the hex string to make it more similar to the linux sha256sum command output
    (mv erp spanfree-tj (acl2::string-downcase sha256-hexstring) state)))


;; Convert JSON AST to ACL2 AST.

(define jsonfile-to-formal-and-sha256 ((filename stringp) state)
  :returns (mv (erp booleanp)
               (ret-file file)
               (hashstring stringp)
               state)
  (b* (((mv erp spanfree-tj sha256-hexstring state) (jsonfile-to-spanfree-and-sha256 filename state))
       ((when erp) (mv t *error-file* sha256-hexstring state)) ; ignore the error spanfree-tj for now
       ((mv erp ast) (j2f-file spanfree-tj)))
    (mv erp ast sha256-hexstring state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run jsonfile-to-formal on a list of json files and report.

(define jsonfile-to-formal-tests-aux ((remaining-filenames string-listp)
                                      state)
  :returns (mv (ok-files true-listp) (fail-files true-listp) state)
  (if (endp remaining-filenames)
      (mv nil nil state)
    (b* (((mv erp ?leo-file state)
          (jsonfile-to-formal (first remaining-filenames) state))
         ((mv rest-ok-files rest-fail-files state)
          (jsonfile-to-formal-tests-aux (rest remaining-filenames) state)))
      (if (not erp)
          (mv (cons (first remaining-filenames) rest-ok-files)
              rest-fail-files
              state)
        (mv rest-ok-files
            (cons (first remaining-filenames) rest-fail-files)
            state)))))

(define jsonfile-to-formal-tests ((filenames-filename stringp) state)
  :returns (mv (fraction-without-error rationalp)
               state)
  (b* (((unless (stringp filenames-filename))
        (prog2$ (cw "first argument to jsonfile-to-formal-tests should be a filename string~%")
                (mv 0 state)))
       ((mv filenames state)
        (acl2::read-file-lines-no-newlines filenames-filename state)
        )
       ((when (stringp filenames))
        (prog2$ (cw "error from acl2::read-file-lines-no-newlines: ~x0~%" filenames)
                (mv 0 state)))
       ((unless (and (true-listp filenames) (string-listp filenames)))
        (prog2$ (cw "error in return type from acl2::read-file-lines-no-newlines~%")
                (mv 0 state)))
       ;; One idiosyncrasy of read-file-lines-no-newlines is
       ;; if the file ends in a newline, it returns an emptystring as the last line.
       ;; In that case we remove it.
       (filenames2 (if (and (consp filenames) (equal (last filenames) '("")))
                      (butlast filenames 1)
                    filenames))
       ;; Suggestion: If we added a rule about butlast we could eliminate a lot of extra checks.
       ;; Probably some of the other checks can also be eliminated.
       ((unless (and (true-listp filenames2) (string-listp filenames2) (not (null filenames2))))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state)))
       ((mv ok-files fail-files state)
        (jsonfile-to-formal-tests-aux filenames2 state))
       ((unless (and (true-listp ok-files)
                     (true-listp fail-files)
                     (= (+ (len ok-files) (len fail-files)) (len filenames2))))
        (prog2$ (er hard? 'top-level "filenames gone missing!")
                (mv 0 state)))
       ((when (equal (len filenames2) 0))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state))))
    ;; Suggestion: improve reporting
    (let ((success-ratio (/ (len ok-files) (len filenames2))))
      (if (= success-ratio 1)
          (prog2$ (cw "Congratulations, all ~x0 files converted without error.~%"
                      (len filenames2))
                  (mv success-ratio state))
        (prog2$ (cw "Success ratio: ~x0~%Failing files: ~x1~%"
                    success-ratio
                    fail-files)
                (mv success-ratio state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note, this is a little old.
;; It takes a separately-generated list of files to parse
;; and does not understand the "namespace" in the block comment in the .leo
;; test files.  We leave it here since it can come in handy for ad-hoc testing.
;; -  EM 2022-05-18.

(define test-parse-leo-file ((filename stringp) state)
  :returns (mv (errp booleanp) (parsesp booleanp) state)
  (b* (((mv contents/nil state) (acl2::read-file-as-string filename state))
       ((unless (stringp contents/nil))
        (mv t nil state))
       (parses? (file-parses-same-fringe? contents/nil)))
    (mv nil parses? state)))

(define leo-parse-tests-aux ((remaining-filenames string-listp)
                             state)
  :returns (mv (ok-files true-listp) (fail-files true-listp) state)
  (if (endp remaining-filenames)
      (mv nil nil state)
    (b* (((mv erp parsesp state)
          (test-parse-leo-file (first remaining-filenames) state))
         ((mv rest-ok-files rest-fail-files state)
          (leo-parse-tests-aux (rest remaining-filenames) state)))
      (if (and (not erp) parsesp)
          (mv (cons (first remaining-filenames) rest-ok-files)
              rest-fail-files
              state)
        (mv rest-ok-files
            (cons (first remaining-filenames) rest-fail-files)
            state)))))

(define leo-parse-tests ((filenames-filename stringp) state)
  :returns (mv (fraction-without-error rationalp)
               state)
  (b* (((unless (stringp filenames-filename))
        (prog2$ (cw "first argument to leo-parse-tests should be a filename string~%")
                (mv 0 state)))
       ((mv filenames state)
        (acl2::read-file-lines-no-newlines filenames-filename state)
        )
       ((when (stringp filenames))
        (prog2$ (cw "error from acl2::read-file-lines-no-newlines: ~x0~%" filenames)
                (mv 0 state)))
       ((unless (and (true-listp filenames) (string-listp filenames)))
        (prog2$ (cw "error in return type from acl2::read-file-lines-no-newlines~%")
                (mv 0 state)))
       ;; One idiosyncrasy of read-file-lines-no-newlines is
       ;; if the file ends in a newline, it returns an emptystring as the last line.
       ;; In that case we remove it.
       (filenames2 (if (and (consp filenames) (equal (last filenames) '("")))
                      (butlast filenames 1)
                    filenames))
       ;; Suggestion: If we added a rule about butlast we could eliminate a lot of extra checks.
       ;; Probably some of the other checks can also be eliminated.
       ((unless (and (true-listp filenames2) (string-listp filenames2) (not (null filenames2))))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state)))
       ((mv ok-files fail-files state)
        (leo-parse-tests-aux filenames2 state))
       ((unless (and (true-listp ok-files)
                     (true-listp fail-files)
                     (= (+ (len ok-files) (len fail-files)) (len filenames2))))
        (prog2$ (er hard? 'top-level "filenames gone missing!")
                (mv 0 state)))
       ((when (equal (len filenames2) 0))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state))))
    ;; Suggestion: improve reporting
    (let ((success-ratio (/ (len ok-files) (len filenames2))))
      (if (= success-ratio 1)
          (prog2$ (cw "Congratulations, all ~x0 files parsed without error.~%"
                      (len filenames2))
                  (mv success-ratio state))
        (prog2$ (cw "Success ratio: ~x0~%Files having parse failure: ~x1~%"
                    success-ratio
                    fail-files)
                (mv success-ratio state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Note, this is based on test-parse-leo-file / leo-parse-tests above,
;; and has the same limitations.  It is handy for ad-hoc testing.
;; -  EM 2022-05-18.

(define test-correct-leo-parse ((json-filename stringp) state)
  :returns (mv (errp booleanp) (checked-correct-p booleanp) state)
  (b* (;; first convert AST from the JSON file to ACL2
       ((mv erp file-ast state) (jsonfile-to-formal json-filename state))
       ((when erp)
        (mv t nil state))
       ;; next, parse the .json file using ACL2.
       ;;  - replace ".json" by ".leo"
       (leo-filename (string-append
                      (subseq json-filename 0 (- (length json-filename) 5))
                      ".leo"))
       ;;  - capture the file contents
       ((mv leo-file-source state) (acl2::read-file-as-string leo-filename state))
       ;;  - parse the file (it is ok to get the file again, that tests another interface function
       ((mv tree lexemes state)
        (parse-from-file-at-path+ leo-filename state))
       ;; make sure the lexeme fringe matches the source
       ((unless (equal (abnf::tree-list->string lexemes) ; actually a codepoint list
                       (acl2::utf8=>ustring (string=>nats leo-file-source))))
        (prog2$ (cw "different fringe from parsing filename ~x0~%" leo-filename)
                (mv t nil state)))
       ;; call abstractor
       (abs-file-equal? (equal (abs-file tree) file-ast))
       ((unless abs-file-equal?)
        (prog2$ (cw "asts were not equal~%" )
                (mv t nil state))))
    (mv nil t state)))

(define test-correct-leo-parses-aux ((remaining-filenames string-listp)
                             state)
  :returns (mv (ok-files true-listp) (fail-files true-listp) state)
  (if (endp remaining-filenames)
      (mv nil nil state)
    (b* (((mv erp parsesp state)
          (test-correct-leo-parse (first remaining-filenames) state))
         ((mv rest-ok-files rest-fail-files state)
          (test-correct-leo-parses-aux (rest remaining-filenames) state)))
      (if (and (not erp) parsesp)
          (mv (cons (first remaining-filenames) rest-ok-files)
              rest-fail-files
              state)
        (mv rest-ok-files
            (cons (first remaining-filenames) rest-fail-files)
            state)))))

;; The argument should be the name of a file that contains a list of json file paths.
(define test-correct-leo-parses ((filenames-filename stringp) state)
  :returns (mv (fraction-without-error rationalp)
               state)
  (b* (((unless (stringp filenames-filename))
        (prog2$ (cw "first argument to test-correct-leo-parses should be a filename string~%")
                (mv 0 state)))
       ((mv filenames state)
        (acl2::read-file-lines-no-newlines filenames-filename state)
        )
       ((when (stringp filenames))
        (prog2$ (cw "error from acl2::read-file-lines-no-newlines: ~x0~%" filenames)
                (mv 0 state)))
       ((unless (and (true-listp filenames) (string-listp filenames)))
        (prog2$ (cw "error in return type from acl2::read-file-lines-no-newlines~%")
                (mv 0 state)))
       ;; One idiosyncrasy of read-file-lines-no-newlines is
       ;; if the file ends in a newline, it returns an emptystring as the last line.
       ;; In that case we remove it.
       (filenames2 (if (and (consp filenames) (equal (last filenames) '("")))
                      (butlast filenames 1)
                    filenames))
       ;; Suggestion: If we added a rule about butlast we could eliminate a lot of extra checks.
       ;; Probably some of the other checks can also be eliminated.
       ((unless (and (true-listp filenames2) (string-listp filenames2) (not (null filenames2))))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state)))
       ((mv ok-files fail-files state)
        (test-correct-leo-parses-aux filenames2 state))
       ((unless (and (true-listp ok-files)
                     (true-listp fail-files)
                     (= (+ (len ok-files) (len fail-files)) (len filenames2))))
        (prog2$ (er hard? 'top-level "filenames gone missing!")
                (mv 0 state)))
       ((when (equal (len filenames2) 0))
        (prog2$ (cw "no filenames in filenames-filename")
                (mv 0 state))))
    ;; Suggestion: improve reporting
    (let ((success-ratio (/ (len ok-files) (len filenames2))))
      (if (= success-ratio 1)
          (prog2$ (cw "Congratulations, all ~x0 files were parsed and checked without error.~%"
                      (len filenames2))
                  (mv success-ratio state))
        (prog2$ (cw "Success ratio: ~x0~%Files having parse or check failure: ~x1~%"
                    success-ratio
                    fail-files)
                (mv success-ratio state))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-file-as-string-and-sha256 ((filename stringp) state)
  :returns (mv (erp booleanp)
               (ret-source stringp)
               (hashstring stringp)
               state)
  (b* (((mv nil/as-string state) (acl2::read-file-as-string filename state))
       ((when (null nil/as-string))
        (mv t "" "" state))
       (contents-as-chars (acl2::explode nil/as-string))
       ;; Although just reading the file again is probably faster than all these
       ;; conversions, it is less secure.
       ;; If we need better performance we can rewrite to do everything in one pass.
       (char-codes (acl2::map-char-code contents-as-chars))
       (sha256-from-bytes (sha2::sha-256-bytes char-codes))
       (sha256-hexstring (acl2::ubyte8s=>hexstring sha256-from-bytes)))
    ;; downcase the hex string to make it more similar to the linux sha256sum command output
    (mv nil nil/as-string (acl2::string-downcase sha256-hexstring) state)))
