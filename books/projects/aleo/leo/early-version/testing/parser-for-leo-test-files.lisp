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

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/string-stringlist-alist" :dir :system)
(include-book "kestrel/fty/maybe-string" :dir :system)
(include-book "std/strings/letter-chars" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/defprojection" :dir :system)

(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Leo source code at https://github.com/AleoHQ/leo (testnet3 branch)
; includes a test framework and a number of tests under the tests/ directory,
; described in the README.md file in that directory.
; Here we introduce data types to capture the tests in that format,
; and a parser that turns test files in that format
; into structured values of these data types for easier processing.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Data types for test information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype of Leo "leotest" test cases.
; A .leo file in the "leo/tests/" directory can turn into multiple
; test cases, either because there are multiple item strings in the
; body of the file (such as for parsing fragments of programs)
; or because there are multiple input files.
; Those two reasons probably can't happen at the same time,
; but since they might in the future, each item string
; cross each input file mentioned gets put into a separate leotest-testcase.
; If no input file is mentioned then the inpath and incontents are NIL
; for each item string.

(fty::defprod leotest-testcase
  ((item string)
   (inpath acl2::maybe-string)
   (incontents acl2::maybe-string))
  :pred leotest-testcasep)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of lists of leotest testcases.

(fty::deflist leotest-testcase-list
  :elt-type leotest-testcase
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-testcase-listp)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of Leo test strings.
; This type is only used when scanning the leotest file for
; test input strings.

(fty::defprod leotest-string
  ((get string))
  :pred leotest-stringp)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of lists of Leo test strings.
; This type is only used when scanning the leotest file for
; test input strings.

(fty::deflist leotest-string-list
  :elt-type leotest-string
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-string-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype of test categories.
; These correspond to the namespace information in the test files.
; The term 'category' seems better than 'namespace', so we use it here.

(fty::deftagsum leotest-category
  (:parse-token ())
  (:parse-expression ())
  (:parse-statement ())
  (:parse-file ())
  (:compile ())
  (:serialize ())
  (:input ())
  (:bench ())
  :pred leotest-categoryp)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of lists of Leo test categories.

(fty::deflist leotest-category-list
  :elt-type leotest-category
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-category-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype of Leo input files paths.
; This type is only used when scanning the leotest file for
; test input strings.

(fty::defprod leotest-inpath
  ((get string))
  :pred leotest-inpathp)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of lists of Leo input file paths.
; This type is only used when scanning the leotest file for
; test input strings.

(fty::deflist leotest-inpath-list
  :elt-type leotest-inpath
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-inpath-listp)

;;;;;;;;;;

; Lift LEOTEST-INPATH to lists.

(std::defprojection string-list-to-leotest-inpath-list (x)
  :guard (string-listp x)
  :returns (paths leotest-inpath-listp)
  (leotest-inpath x)
  ///
  (fty::deffixequiv string-list-to-leotest-inpath-list
    :args ((x string-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; DEPRECATED:
; Fixtype of Leo input files contents.
; These are in parallel to the input file paths.

(fty::defprod leotest-incontents
  ((get string))
  :pred leotest-incontentsp)

;;;;;;;;;;;;;;;;;;;;

;;; DEPRECATED:
; Fixtype of lists of Leo input file contentss.

(fty::deflist leotest-incontents-list
  :elt-type leotest-incontents
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-incontents-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; utility
(define path-dirname ((path stringp))
  :returns (dirname stringp
                    :hyp :guard)
  (b* ((last-slash-pos (search "/" path :from-end t))
       ((unless (and (natp last-slash-pos)
                     (< last-slash-pos (length path))))
        ""))
    (subseq path 0 (+ last-slash-pos 1))))

; Given the input file paths, reads each input file into a string.
(define input-paths-to-contents ((leo-source-dir stringp)
                                 (inpaths leotest-inpath-listp)
                                 state)
  :returns (mv (contents-list string-listp)
               state)
  (b* (((when (endp inpaths))
        (mv nil state))
       (first-inpath (first inpaths))
       (first-instring (leotest-inpath->get first-inpath))
       (first-contents-or-nil (acl2::read-file-into-string
                               (string-append leo-source-dir
                                              first-instring)))
       (first-contents-string (if (stringp first-contents-or-nil)
                                  first-contents-or-nil
                                ""))
       ((mv rest-contents-strings state)
        (input-paths-to-contents leo-source-dir (rest inpaths) state))
       )
    (mv (cons first-contents-string rest-contents-strings)
        state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Fixtype of Leo test files.
; A value of this type represents the information in one Leo test file,
; parsed from the file intro a structured form.
; Besides the category, there is a pass/fail expectation,
; encoded as a boolean that is true for pass and false for fail.
; The actual tests are a list of zero or more of leotest-testcase.
;
; For the categories :PARSE-FILE, :COMPILE, :SERIALIZE, and :INPUT,
; There will be one testcase item string, and if there is more than one
; input file, there will be a separate testcase for each input file.

(fty::defprod leotest-file
  ((path string)
   (category leotest-category)
   (passp bool)
   (testcases leotest-testcase-list))
  :pred leotest-filep)

;;;;;;;;;;;;;;;;;;;;

; Fixtype of lists of Leo test files.

(fty::deflist leotest-file-list
  :elt-type leotest-file
  :true-listp t
  :elementp-of-nil nil
  :pred leotest-file-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parser of Leo test files into the data types above.
; Most of the parser's functions operate on lists of ACL2 characters,
; which must be viewed as sequences of 8-bit characters,
; whose codes must be viewed as UTF-8 bytes that form the Leo test files.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consume the body of a YAML comment.
; A YAML comment starts with '#' and ends at the end of the line or file.
; Here by 'body' we mean the comment without the initial '#',
; which is recognized and consumed by the caller of this function.
; The end of line is either a CR or a LF character,
; which is also consumed by this function.
; If the line is actually terminated by CR LF (e.g. on Windows),
; the LF is left unconsumed, but this is not a problem,
; because this function is only called by LEOTEST-SKIP-WHITESPACE/COMMENTS,
; which will proceed to skip over the LF and any subsequent whitespace/comment.

(define leotest-consume-yaml-comment-body ((chars character-listp))
  :returns (rest-chars character-listp :hyp :guard)
  (cond ((endp chars) nil)
        ((or (eql (car chars) #\Return)
             (eql (car chars) #\Newline))
         (cdr chars))
        (t (leotest-consume-yaml-comment-body (cdr chars))))
  ///

  (more-returns
   (rest-chars true-listp
               :hyp (true-listp chars)
               :rule-classes :type-prescription))

  (defret len-of-leotest-consume-yaml-comment-body
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Skip whitespace and YAML comments,
; till reaching end of input or non-whitespace/non-comment.

(define leotest-skip-whitespace/comments ((chars character-listp))
  :returns (rest-chars character-listp :hyp :guard)
  (cond ((endp chars) nil)
        ((or (eql (car chars) #\Space)
             (eql (car chars) #\Tab)
             (eql (car chars) #\Return)
             (eql (car chars) #\Newline))
         (leotest-skip-whitespace/comments (cdr chars)))
        ((eql (car chars) #\#)
         (leotest-skip-whitespace/comments
          (leotest-consume-yaml-comment-body (cdr chars))))
        (t chars))
  :measure (len chars)
  ///

  (more-returns
   (rest-chars true-listp
               :hyp (true-listp chars)
               :rule-classes :type-prescription))

  (defret len-of-leotest-skip-whitespace/comments
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consume the opening of the block comment "/*".
; Error if not found.

(define leotest-consume-opening ((chars character-listp))
  :returns (mv err? (rest-chars character-listp :hyp :guard))
  (if (and (consp chars)
           (consp (cdr chars))
           (prefixp (str::explode "/*") chars))
      (mv nil (cddr chars))
    (mv :no-opening-of-block-comment nil))
  ///

  (defret len-of-leotest-consume-opening
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consume the closing of the block comment "*/".
; Error if not found.

(define leotest-consume-closing ((chars character-listp))
  :returns (mv err? (rest-chars character-listp :hyp :guard))
  (if (and (consp chars)
           (consp (cdr chars))
           (prefixp (str::explode "*/") chars))
      (mv nil (cddr chars))
    (mv :no-closing-of-block-comment nil))
  ///

  (defret len-of-leotest-consume-closing
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a word, i.e. a contiguous non-empty sequence of letters and underscores.
; Return it as a string.
; Stop when end of input or other kind of character is encountered.

(define leotest-parse-word-loop ((chars character-listp)
                                 (word-chars-rev character-listp))
  :returns (mv (word-chars character-listp :hyp :guard)
               (rest-chars character-listp
                           :hyp (character-listp chars)))
  (if (or (endp chars)
          (and (not (str::letter-char-p (car chars)))
               (not (eql (car chars) #\_))))
      (mv (rev word-chars-rev) chars)
    (leotest-parse-word-loop (cdr chars)
                             (cons (car chars) word-chars-rev)))
  ///

  (more-returns
   (word-chars true-listp :rule-classes :type-prescription))

  (defret len-of-leotest-parse-word-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-word ((chars character-listp))
  :returns (mv err?
               (word stringp)
               (rest-chars character-listp :hyp :guard))
  (b* (((mv word-chars chars) (leotest-parse-word-loop chars nil))
       ((when (endp word-chars)) (mv :empty-word "" nil)))
    (mv nil (str::implode word-chars) chars))
  ///

  (defret len-of-leotest-parse-word
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consume a colon.
; Error if not found.

(define leotest-consume-colon ((chars character-listp))
  :returns (mv err? (rest-chars character-listp :hyp :guard))
  (if (and (consp chars)
           (eql (car chars) #\:))
      (mv nil (cdr chars))
    (mv :no-colon nil))
  ///

  (defret len-of-leotest-consume-colon
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a path, i.e. a contiguous non-empty sequence of
; letters, digits, underscores, dots, and slashes.
; These are all the characters that we expect to be used in paths;
; it is not hard to add more if needed.
; Stop when end of input or other kind of character is encountered.

(define leotest-parse-path-loop ((chars character-listp)
                                 (path-chars-rev character-listp))
  :returns (mv (path-chars character-listp :hyp :guard)
               (rest-chars character-listp :hyp (character-listp chars)))
  (if (or (endp chars)
          (and (not (str::letter-char-p (car chars)))
               (not (str::dec-digit-char-p (car chars)))
               (not (member (car chars) '(#\_ #\. #\/)))))
      (mv (rev path-chars-rev) chars)
    (leotest-parse-path-loop (cdr chars)
                             (cons (car chars) path-chars-rev)))
  ///

  (more-returns
   (path-chars true-listp :rule-classes :type-prescription))

  (defret len-of-leotest-parse-path-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-path ((chars character-listp))
  :returns (mv err?
               (path stringp)
               (rest-chars character-listp :hyp :guard))
  (b* (((mv path-chars chars) (leotest-parse-path-loop chars nil))
       ((when (endp path-chars)) (mv :empty-path "" nil)))
    (mv nil (str::implode path-chars) chars))
  ///

  (defret len-of-leotest-parse-path
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Consume a dash.
; Error if not found.

(define leotest-consume-dash ((chars character-listp))
  :returns (mv err? (rest-chars character-listp :hyp :guard))
  (if (and (consp chars)
           (eql (car chars) #\-))
      (mv nil (cdr chars))
    (mv :no-dash nil))
  ///

  (defret len-of-leotest-consume-dash
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a sequence of paths (of Leo input files),
; each preceded by a dash,
; as they appear in the YAML in a Leo test file.
; Stop when there is no more dash.

(define leotest-parse-paths-loop ((chars character-listp)
                                  (paths-rev string-listp))
  :returns (mv err?
               (paths string-listp :hyp (string-listp paths-rev))
               (rest-chars character-listp :hyp (character-listp chars)))
  (b* ((chars0 chars)
       (chars (leotest-skip-whitespace/comments chars))
       ((when (or (endp chars)
                  (not (eql (car chars) #\-))))
        (mv nil (rev paths-rev) chars))
       ((mv err? chars) (leotest-consume-dash chars))
       ((when err?) (mv err? nil nil))
       (chars (leotest-skip-whitespace/comments chars))
       ((mv err? path chars) (leotest-parse-path chars))
       ((when err?) (mv err? nil nil))
       ((unless (mbt (< (len chars) (len chars0)))) (mv :impossible nil nil)))
    (leotest-parse-paths-loop chars (cons path paths-rev)))
  :measure (len chars)
  ///

  (more-returns
   (paths true-listp :rule-classes :type-prescription))

  (defret len-of-leotest-parse-paths-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-paths ((chars character-listp))
  :returns (mv err?
               (paths string-listp)
               (rest-chars character-listp :hyp :guard))
  (b* (((mv err? paths chars) (leotest-parse-paths-loop chars nil))
       ((when err?) (mv err? nil nil))
       ((unless (consp paths)) (mv :no-paths nil nil)))
    (mv nil paths chars))
  ///

  (defret len-of-leotest-parse-paths
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse either a single file path or a sequence of file paths;
; in the latter case, each preceded by a dash.
; This parse the possible values of the input_file key in the YAML.

(define leotest-parse-path/s ((chars character-listp))
  :returns (mv err?
               (path/s string-listp)
               (rest-chars character-listp :hyp :guard))
  (b* ((chars (leotest-skip-whitespace/comments chars)))
    (if (and (consp chars)
             (eql (car chars) #\-))
        (b* (((mv err? paths chars) (leotest-parse-paths chars))
             ((when err?) (mv err? nil nil)))
          (mv nil paths chars))
      (b* (((mv err? path chars) (leotest-parse-path chars))
           ((when err?) (mv err? nil nil)))
        (mv nil (list path) chars))))
  ///

  (defret len-of-leotest-parse-path/s
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read a sequence of YAML "key:val" pairs,
; putting the result in a finite map (i.e. alist).
; The keys of the alist are strings, which we normalize to lowercase.
; The values of the alist are either single strings or lists of strings.
; At each loop iteration,
; based on the key we find,
; we either parse a single string, which we normalize to lowercase,
; or something that may be a single string or a list of strings,
; which we do not normalize to lowercase.

(define leotest-parse-yaml-loop ((chars character-listp)
                                 (map string-stringlist-alistp))
  :returns (mv err?
               (new-map string-stringlist-alistp
                        :hyp (string-stringlist-alistp map))
               (rest-chars character-listp :hyp (character-listp chars)))
  (b* ((chars (leotest-skip-whitespace/comments chars))
       ((when (and (consp chars)
                   (eql (car chars) #\*)))
        (mv nil map chars))
       ((mv err? key chars) (leotest-parse-word chars))
       ((when err?) (mv err? nil nil))
       (key (str::downcase-string key))
       (chars (leotest-skip-whitespace/comments chars))
       ((mv err? chars) (leotest-consume-colon chars))
       ((when err?) (mv err? nil nil))
       (chars (leotest-skip-whitespace/comments chars))
       ((mv err? val chars)
        (cond ((or (equal key "namespace")
                   (equal key "expectation"))
               (b* (((mv err? val chars) (leotest-parse-word chars))
                    ((when err?) (mv err? nil nil))
                    (val (str::downcase-string val)))
                 (mv nil (list val) chars)))
              ((equal key "input_file")
               (leotest-parse-path/s chars))
              (t (mv :unsupported-key nil nil))))
       ((when err?) (mv err? nil nil))
       ((when (consp (assoc-equal key map)))
        (mv :duplicate-yaml-key nil nil)))
    (leotest-parse-yaml-loop chars (acons key val map)))
  :measure (len chars)
  ///

  (defret len-of-leotest-parse-yaml-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-yaml ((chars character-listp))
  :returns (mv err?
               (map string-stringlist-alistp)
               (rest-chars character-listp :hyp :guard))
  (leotest-parse-yaml-loop chars nil)
  ///

  (defret len-of-leotest-parse-yaml
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse the header of the Leo test files,
; i.e. the block comment with the YAML.
; Return a map with the YAML information
; and the remaining characters of the file
; after skipping whitespace after the closing "*/".

(define leotest-parse-header ((chars character-listp))
  :returns (mv err?
               (map string-stringlist-alistp)
               (rest-chars character-listp :hyp :guard))
  (b* ((chars (leotest-skip-whitespace/comments chars))
       ((mv err? chars) (leotest-consume-opening chars))
       ((when err?) (mv err? nil nil))
       ((mv err? map chars) (leotest-parse-yaml chars))
       ((when err?) (mv err? nil nil))
       ((mv err? chars) (leotest-consume-closing chars))
       ((when err?) (mv err? nil nil))
       (chars (leotest-skip-whitespace/comments chars)))
    (mv nil map chars))
  ///

  (defret len-of-leotest-parse-header
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a line, i.e. a non-empty sequence of characters except CR and LF.
; Error if the line is empty.

(define leotest-parse-line-loop ((chars character-listp)
                                 (line-chars-rev character-listp))
  :returns (mv (line-chars character-listp :hyp :guard)
               (rest-chars character-listp
                           :hyp (character-listp chars)))
  (if (or (endp chars)
          (member (car chars) '(#\Newline #\Return)))
      (mv (rev line-chars-rev) chars)
    (leotest-parse-line-loop (cdr chars) (cons (car chars) line-chars-rev)))
  ///

  (more-returns
   (line-chars true-listp :rule-classes :type-prescription))

  (defret len-of-leotest-parse-line-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-line ((chars character-listp))
  :returns (mv err?
               (line stringp)
               (rest-chars character-listp :hyp :guard))
  (b* (((mv line-chars rest-chars) (leotest-parse-line-loop chars nil))
       ;; TODO: replace this test with (CONSP LINE-CHARS)
       ;; (needs a slightly more elaborate proof of DEFRET below):
       ((unless (< (len rest-chars) (len chars))) (mv :empty-line "" nil)))
    (mv nil (str::implode line-chars) rest-chars))
  ///

  (defret len-of-leotest-parse-line
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse all the non-empty lines remaining in the file,
; returning a corresponding list of Leo test strings.

(define leotest-parse-lines-loop ((chars character-listp)
                                  (test-strings-rev leotest-string-listp))
  :returns (mv err?
               (test-strings leotest-string-listp
                             :hyp (leotest-string-listp test-strings-rev))
               (rest-chars character-listp))
  (b* (((when (endp chars)) (mv nil (rev test-strings-rev) nil))
       ((mv err? line chars) (leotest-parse-line chars))
       ((when err?) (mv err? nil nil))
       (chars (leotest-skip-whitespace/comments chars)))
    (leotest-parse-lines-loop chars
                              (cons (leotest-string line)
                                    test-strings-rev)))
  :measure (len chars)
  ///

  (defret len-of-leotest-parse-lines-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-lines ((chars character-listp))
  :returns (mv err? (test-strings leotest-string-listp))
  (b* (((mv err? test-strings &) (leotest-parse-lines-loop chars nil))
       ((when err?) (mv err? nil)))
    (mv nil test-strings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse a block, i.e. a non-empty sequence of characters
; not including blank lines,
; where a blank line is either LF LF or CR LF CR LF.
; Error if the block is empty.

(define leotest-parse-block-loop ((chars character-listp)
                                  (block-chars-rev character-listp))
  :returns (mv (block-chars character-listp :hyp :guard)
               (rest-chars character-listp
                           :hyp (character-listp chars)))
  (if (or (endp chars)
          (prefixp (list #\Newline #\Newline) chars)
          (prefixp (list #\Return #\Newline #\Return #\Newline) chars))
      (mv (rev block-chars-rev) chars)
    (leotest-parse-block-loop (cdr chars) (cons (car chars) block-chars-rev)))
  ///

  (more-returns
   (block-chars true-listp :rule-classes :type-prescription))

  (defret len-of-leotest-parse-block-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-block ((chars character-listp))
  :returns (mv err?
               (block stringp)
               (rest-chars character-listp :hyp :guard))
  (b* (((mv block-chars rest-chars) (leotest-parse-block-loop chars nil))
       ;; TODO:replace this test with (CONSP BLOCK-CHARS)
       ;; (needs a slightly more elaborate proof of DEFRET below):
       ((unless (< (len rest-chars) (len chars))) (mv :empty-block "" nil)))
    (mv nil (str::implode block-chars) rest-chars))
  ///

  (defret len-of-leotest-parse-block
    (implies (not err?)
             (< (len rest-chars)
                (len chars)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse all the non-empty blocks remaining in the file,
; returning a corresponding list of Leo test strings.

(define leotest-parse-blocks-loop ((chars character-listp)
                                   (test-strings-rev leotest-string-listp))
  :returns (mv err?
               (test-strings leotest-string-listp
                             :hyp (leotest-string-listp test-strings-rev))
               (rest-chars character-listp))
  (b* (((when (endp chars)) (mv nil (rev test-strings-rev) nil))
       ((mv err? block chars) (leotest-parse-block chars))
       ((when err?) (mv err? nil nil))
       (chars (leotest-skip-whitespace/comments chars)))
    (leotest-parse-blocks-loop chars
                              (cons (leotest-string block)
                                    test-strings-rev)))
  :measure (len chars)
  ///

  (defret len-of-leotest-parse-blocks-loop
    (<= (len rest-chars)
        (len chars))
    :rule-classes :linear))

(define leotest-parse-blocks ((chars character-listp))
  :returns (mv err? (test-strings leotest-string-listp))
  (b* (((mv err? test-strings &) (leotest-parse-blocks-loop chars nil))
       ((when err?) (mv err? nil)))
    (mv nil test-strings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; leotest-parse-file section

; Parse (the characters of) the whole Leo test file.
; First we parse the header, obtaining a map.
; The map must contain "namespace" and "expectation",
; and if it has "input_file" we also record that.
;
; Based on the namespace, we create tests consisting of
; lines, blocks, or the rest of the file.

; A dummy value that can be returned by leotest-parse-file to
; indicate an error
(defmacro mv-irr-file ()
  '(mv nil "dummy" (leotest-category-compile) nil nil nil))

(define leotest-parse-file ((chars character-listp) (path stringp))
  :returns (mv (expectation-skip? booleanp)
               (path stringp :hyp :guard)
               (category leotest-categoryp)
               (passp booleanp)
               (tests leotest-string-listp)
               (inpaths leotest-inpath-listp))

  ;; Raises an error if file can't be parsed into a leotest-filep;
  ;; logically returns the dummy tuple (mv-irr-file) in that case.
  ;; The parameter `path` is just for recording in the leotest-file returned.
  (b* (((mv err? map chars) (leotest-parse-header chars))
       ((when err?)
        (raise "For test file: ~x0~%Failed to parse header: ~x1" path err? )
        (mv-irr-file))
       (namespace (assoc-equal "namespace" map))
       ((unless (consp namespace))
        (raise "Missing namespace.")
        (mv-irr-file))
       (namespace (cdr namespace))
       ((unless (= (len namespace) 1))
        (raise "Impossible: namespace ~x0" namespace)
        (mv-irr-file))
       (namespace (car namespace))
       (category (cond ((equal namespace "input")
                        (leotest-category-input))
                       ((equal namespace "bench")
                        (leotest-category-bench))
                       ((equal namespace "serialize")
                        (leotest-category-serialize))
                       ((equal namespace "compile")
                        (leotest-category-compile))
                       ((equal namespace "parse")
                        (leotest-category-parse-file))
                       ((equal namespace "parsestatement")
                        (leotest-category-parse-statement))
                       ((equal namespace "parseexpression")
                        (leotest-category-parse-expression))
                       ((equal namespace "token")
                        (leotest-category-parse-token))
                       (t nil)))
       ((unless category)
        (raise "For test file: ~x0~%Bad namespace: ~x1" path namespace)
        (mv-irr-file))
       (expectation (assoc-equal "expectation" map))
       ((unless (consp expectation))
        (raise "Missing expectation.")
        (mv-irr-file))
       (expectation (cdr expectation))
       ((unless (= (len expectation) 1))
        (raise "Impossible: expectation ~x0" expectation)
        (mv-irr-file))
       (expectation (car expectation))
       (skip? (equal expectation "skip"))
       (passp (cond (skip? nil)
                    ((equal expectation "pass") t)
                    ((equal expectation "fail") nil)
                    (t (raise "Bad expectation: ~x0" expectation))))
       (inpaths
        (b* ((inputfiles (assoc-equal "input_file" map))
             ((unless (consp inputfiles)) nil)
             (inputfiles (cdr inputfiles)))
          (string-list-to-leotest-inpath-list inputfiles)))
       (tests
        (leotest-category-case
         category
         :bench
         (list (leotest-string (str::implode chars)))
         :input
         (list (leotest-string (str::implode chars)))
         :serialize
         (list (leotest-string (str::implode chars)))
         :compile
         (list (leotest-string (str::implode chars)))
         :parse-file
         (list (leotest-string (str::implode chars)))
         :parse-statement
         (b* (((mv err? tests) (leotest-parse-blocks chars))
              ((when err?)
               (raise "Failed to parse blocks: ~x0" err?)))
           tests)
         :parse-expression
         (b* (((mv err? tests) (leotest-parse-lines chars))
              ((when err?)
               (raise "Failed to parse lines: ~x0" err?)))
           tests)
         :parse-token
         (b* (((mv err? tests) (leotest-parse-lines chars))
              ((when err?)
               (raise "Failed to parse lines: ~x0" err?)))
           tests))))
    (mv skip? path category passp tests inpaths)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; making testcases from tests X input-contents

;; If there are no inputs for a given leotest-string, make a single testcase.
(define make-single-testcase-for-test ((test leotest-stringp))
  :returns (case leotest-testcasep)
  (make-leotest-testcase :item (leotest-string->get test)
                         :inpath nil
                         :incontents nil))

;; If there is one or more inputs for a given leotest string,
;; name a test case for each of them by calling this function.
(define make-testcases-for-test ((test leotest-stringp)
                                 (inpaths leotest-inpath-listp)
                                 (input-contents string-listp))
  :returns (cases leotest-testcase-listp)
  ;; Although we check that the lists are the same length in the caller,
  ;; this is still a good check.
  (if (or (endp inpaths) (endp input-contents))
      nil
    (cons (make-leotest-testcase :item (leotest-string->get test)
                                 :inpath (leotest-inpath->get (first inpaths))
                                 :incontents (first input-contents))
          (make-testcases-for-test test
                                   (rest inpaths)
                                   (rest input-contents)))))

;; Makes a test case for each test X inpath.
(define make-testcases-for-tests ((tests leotest-string-listp)
                                  (inpaths leotest-inpath-listp)
                                  (input-contents string-listp))
  :returns (cases leotest-testcase-listp)
  (if (endp tests)
      nil
    (b* ((first-test (first tests))
         (first-cases (if (null inpaths)
                          (list (make-single-testcase-for-test first-test))
                        (make-testcases-for-test first-test
                                                 inpaths
                                                 input-contents)))
         (rest-cases (make-testcases-for-tests (rest tests)
                                               inpaths
                                               input-contents)))
      (append first-cases rest-cases))))

(define make-leotest-file-from-data ((path stringp)
                                     (category leotest-categoryp)
                                     (passp booleanp)
                                     (tests leotest-string-listp)
                                     (inpaths leotest-inpath-listp)
                                     (input-contents string-listp))
  :returns (test-file leotest-filep)
  (let ((cases (make-testcases-for-tests tests inpaths input-contents)))
    (make-leotest-file :path path
                       :category category
                       :passp passp
                       :testcases cases)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; leotest-parse-file-at-path section

; A dummy value that can be returned by leotest-parse-file-at-path
(defconst *irr-file*
  (make-leotest-file :path "dummy"
                     :category (leotest-category-compile)
                     :passp nil
                     :testcases nil))

; Parse the Leo test file.
; By that, we mean to parse a .leo file under `root-dir`.
; The file must have "namespace" and "expectation" fields in a comment
; in the header.
; Some of them are whole Leo programs,
; but some have Leo fragments such as tokens, expressions, or statements.
; The path to to the file parsed is (string-append root-dir path).
; Additionally, if there is one or more input file mentioned, those
; files are read into strings within testcases.
; Returns a value of type leotest-filep.

(define leotest-parse-file-at-path ((root-dir stringp) (path stringp) state)
  :returns (mv (test-file leotest-filep) state)
  ;; Raises an error if file can't be parsed into a leotest-filep
  ;; We may want to catch and report on these errors.
  (b* (((mv err/contents state)
        (acl2::read-file-characters (string-append root-dir path) state))
       ((unless (listp err/contents))
        (raise "Problem reading file at path: ~x0" err/contents)
        ;; Execution can't pass (raise),
        ;; but logically returns the irrelevant leotest-file.
        (mv *irr-file* state))

       ((mv skip? parsed-path category passp tests inpaths)
        (leotest-parse-file err/contents path))

       ;; For now, make skip? return *irr-file* and make callers filter
       ;; them out or handle as desired.
       ;; We may want to model skip? in the future, though, in which case
       ;; we would add the field to leotest-file and return a regular
       ;; leotest-file here.
       ((when skip?)
        (mv *irr-file* state))

       ((mv input-files-contents-list state)
        (input-paths-to-contents (string-append root-dir (path-dirname path))
                                 inpaths
                                 state))

       ;; Extra check.
       ((unless (equal (len inpaths) (len input-files-contents-list)))
        (raise "Problem with input files: ~x0" input-files-contents-list)
        ;; Execution can't pass (raise),
        ;; but logically returns the irrelevant leotest-file.
        (mv *irr-file* state))

       (ltf (make-leotest-file-from-data parsed-path
                                         category
                                         passp
                                         tests
                                         inpaths
                                         input-files-contents-list)))
    (mv ltf state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lift LEOTEST-PARSE-FILE-AT-PATH to lists of paths.

(define leotest-parse-files-at-paths ((root-dir stringp)
                                      (paths string-listp)
                                      state)
  :returns (mv (test-files leotest-file-listp) state)
  (b* (((when (endp paths))
        (mv nil state))
       ((mv first-test-file state) (leotest-parse-file-at-path root-dir
                                                               (car paths)
                                                               state))
       ((mv rest-test-files state) (leotest-parse-files-at-paths root-dir
                                                                 (cdr paths)
                                                                 state)))
    (mv (cons first-test-file rest-test-files)
        state)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Filter a list of LEOTEST-FILE

(define leotest-files-filter ((leotest-files leotest-file-listp)
                              (keep-categories leotest-category-listp)
                              (keep-pass-or-not boolean-listp))
  :returns (filtered-files leotest-file-listp
                           :hyp :guard)
  (if (endp leotest-files)
      nil
    (b* ((ltf (first leotest-files))
         (keep-due-to-category? (member-equal (leotest-file->category ltf)
                                              keep-categories))
         (keep-due-to-expected-outcome? (member (leotest-file->passp ltf)
                                                keep-pass-or-not))
         (rest-kept-files (leotest-files-filter (cdr leotest-files)
                                                keep-categories
                                                keep-pass-or-not)))
      (if (and keep-due-to-category? keep-due-to-expected-outcome?)
          (cons ltf rest-kept-files)
        rest-kept-files))))
