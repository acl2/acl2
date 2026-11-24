; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "../../tokenizer")
(include-book "../../token-tree-builder")
(include-book "../../extra-grammatical-restrictions")
(include-book "../../input-format")

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/file-io-light/write-objects-to-file" :dir :system)

; The ACL2 side of the differential tests of the input layer, the lexer,
; the tokenizer, and the token-tree builder
; (see the xdoc topic differential-testing, and README.md in this directory).
; Each entry point reads a file of test inputs
; written by to_acl2.py or by input_format.py,
; runs the front end on each input,
; and writes a file of results, or returns a summary,
; for the comparison scripts in this directory.
; The functions are not in the manual (:parents nil):
; they are tools for testing, not part of the library.

(local (in-theory (enable abnf::tree-listp-when-result-not-error
                          lexemep-when-result-not-error
                          token+span-listp-when-result-not-error
                          token-tree-listp-when-result-not-error
                          source-textp-when-result-not-error)))

(defrulel nat-listp-of-nthcdr
  (implies (nat-listp x)
           (nat-listp (nthcdr n x)))
  :induct t
  :enable nthcdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Input and output.

; A test is ("id" cp1 cp2 ...): a name and the code points of the input.

(define rv-testp (x)
  :returns (yes/no booleanp)
  :parents nil
  (and (consp x)
       (stringp (car x))
       (nat-listp (cdr x))))

(std::deflist rv-test-listp (x)
  (rv-testp x)
  :parents nil
  :true-listp t
  :elementp-of-nil nil)

; Read the tests from a file, which holds them as a single list.
; If the file cannot be read, or does not hold a list of tests,
; print a message and return no tests.

(define rv-read-tests ((fname stringp) state)
  :returns (mv (tests rv-test-listp) state)
  :parents nil
  (b* (((mv erp objects state) (acl2::read-objects-from-file fname state))
       ((when erp)
        (prog2$ (cw "Cannot open ~x0.~%" fname)
                (mv nil state)))
       (tests (and (consp objects) (car objects)))
       ((unless (rv-test-listp tests))
        (prog2$ (cw "~x0 does not hold a list of tests.~%" fname)
                (mv nil state))))
    (mv tests state))
  ///

  (defrule state-p-of-rv-read-tests
    (implies (and (stringp fname)
                  (state-p state))
             (state-p (mv-nth 1 (rv-read-tests fname state))))))

; Write the results to a file, one object after the other.

(define rv-write ((results true-listp) (fname stringp) state)
  :returns state
  :parents nil
  (b* (((mv & state)
        (acl2::write-objects-to-file results fname 'rv-write state)))
    state))

; The code points of a test of to_acl2.py are those of a piece of a file,
; as written.  rustc reads the file with the input layer's steps,
; of which CRLF normalization applies to a piece that is not at the start.

(define rv-normalize ((nats nat-listp))
  :returns (new-nats nat-listp)
  :parents nil
  (b* (((mv new-nats &) (normalize-crlf nats)))
    new-nats))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Counting token trees as the macros of run_rustc.py do.
; rustc turns an outer doc comment into the tokens of #[doc = "..."]
; and an inner one into those of #![doc = "..."].

; Number of top-level token trees.

(define rv-tt-count ((trees token-tree-listp) (acc natp))
  :returns (count natp :hyp (natp acc))
  :parents nil
  (b* (((when (endp trees)) acc)
       (tree (car trees))
       (n (token-tree-case
           tree
           :leaf (b* ((tok (token+span->token tree.token)))
                   (token-case
                    tok
                    :doc-comment (if (equal tok.style (doc-style-outer)) 2 3)
                    :otherwise 1))
           :delimited 1)))
    (rv-tt-count (cdr trees) (+ acc n))))

; Number of tokens at all depths, a delimited group counting as one
; plus its contents (the --deep count of run_rustc.py):
; that is every token but the closing delimiters.
; This is for tokens that the token-tree builder accepts.

(define rv-deep-count ((tokens token+span-listp) (acc natp))
  :returns (count natp :hyp (natp acc))
  :parents nil
  (b* (((when (endp tokens)) acc)
       (tok (token+span->token (car tokens)))
       (n (token-case
           tok
           :close-delim 0
           :doc-comment (if (equal tok.style (doc-style-outer)) 5 6)
           :otherwise 1)))
    (rv-deep-count (cdr tokens) (+ acc n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The probe of run_rustc.py puts each input between the parentheses
; of a macro invocation.  So rustc builds token trees from
; the opening parenthesis, the tokens of the input,
; and the closing parenthesis
; (the rest of the probe's file is balanced, and does not affect
; whether there is an error about delimiters, or which is the first).
; We give the token-tree builder the same tokens.

(define rv-probe-tokens ((tokens token+span-listp))
  :returns (probe-tokens token+span-listp)
  :parents nil
  (cons (make-token+span :token (token-open-delim (delim-paren))
                         :span (irr-span))
        (append (token+span-list-fix tokens)
                (list (make-token+span :token (token-close-delim (delim-paren))
                                       :span (irr-span))))))

; The kind of an error of the token-tree builder, named after
; rustc's three errors about delimiters.

(define rv-delim-error ((err reserrp))
  :parents nil
  (b* ((info (fty::reserr->info err))
       (frame (and (consp info) (car info)))
       (payload (and (consp frame) (consp (cdr frame)) (cadr frame)))
       (kind (and (consp payload) (car payload))))
    (case kind
      (:mismatched-closing-delimiter :mismatched)
      (:unclosed-delimiter :unclosed)
      (:unexpected-closing-delimiter :unexpected)
      (t :other))))

; Short inputs: (rv-go in out edition state) writes, for each test,
; ("id" x), where x is one of the following.
; - :err if the lexer or tokenizer rejects the input.
; - :mismatched, :unclosed, or :unexpected if the token-tree builder
;   rejects the probe's tokens, with that kind of error.
; - :split if the builder accepts the probe's tokens,
;   but the input closes the probe's parenthesis before its end,
;   as ") (" does: the input is not the arguments of the macro,
;   and there is nothing to count
;   (rustc builds the token trees, and reports an error later).
; - Otherwise, the number of top-level token trees of the input.
; It returns the number of tests.

(define rv-run1 ((nats nat-listp) (edition rust::editionp))
  :parents nil
  (b* ((nats (rv-normalize nats))
       (toks (tokenize-rust nats edition "t"))
       ((when (reserrp toks)) :err)
       (trees (build-token-trees (rv-probe-tokens toks)))
       ((when (reserrp trees)) (rv-delim-error trees))
       ((unless (and (consp trees) (not (consp (cdr trees))))) :split)
       (tree (car trees)))
    (token-tree-case tree
                     :leaf :split
                     :delimited (rv-tt-count tree.trees 0))))

(define rv-run ((tests rv-test-listp) (edition rust::editionp) (acc true-listp))
  :returns (results true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp tests)
      (revappend acc nil)
    (rv-run (cdr tests)
            edition
            (cons (list (caar tests) (rv-run1 (cdar tests) edition)) acc)))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go ((in stringp) (out stringp) (edition rust::editionp) state)
  :returns (mv (n natp) state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       (state (rv-write (rv-run tests edition nil) out state)))
    (mv (len tests) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Whole files: (rv-go-files in out state) writes, for each file,
; ("id" n) with the deep token count, ("id" :unbal),
; ("id" (:tokerr)) if only the tokenizer rejects the file, or
; ("id" (:lexerr before at)) with up to 20 code points before
; and 30 code points at the place where lexing stops.
; It returns the number of files.

(define rv-file1 ((nats nat-listp))
  :parents nil
  (b* ((nats (rv-normalize nats))
       ((mv & rest) (lex-*-lexeme nats))
       ((when (consp rest))
        (b* ((pos (nfix (- (len nats) (len rest)))))
          (list :lexerr
                (take (min 20 pos) (nthcdr (nfix (- pos 20)) nats))
                (take (min 30 (len rest)) rest))))
       (toks (tokenize-rust nats (rust::edition-2021) "t"))
       ((when (reserrp toks)) (list :tokerr))
       ((when (reserrp (build-token-trees toks))) :unbal))
    (rv-deep-count toks 0)))

(define rv-files ((tests rv-test-listp) (acc true-listp))
  :returns (results true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp tests)
      (revappend acc nil)
    (rv-files (cdr tests)
              (cons (list (caar tests) (rv-file1 (cdar tests))) acc)))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go-files ((in stringp) (out stringp) state)
  :returns (mv (n natp) state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       (state (rv-write (rv-files tests nil) out state)))
    (mv (len tests) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The lexer against its specification: (rv-go-spec in state) returns
; a list of the number of inputs that lex, and the ids of those among
; them whose lexeme CSTs violate an executable conjunct of lexing-okp,
; that is, every conjunct except maximal munch.
; There should be no such ids.

(define rv-spec-okp ((trees abnf::tree-listp) (input nat-listp))
  :returns (yes/no booleanp)
  :parents nil
  (or (endp trees)
      (b* ((tree (car trees))
           (rest (nthcdr (len (abnf::tree->string tree)) input)))
        (and (lexeme-cst-okp tree)
             (lexeme-cst-doc-comment-cr-okp tree)
             (lexeme-cst-float-period-okp tree rest)
             (lexeme-cst-reserved-number-okp tree rest)
             (lexeme-cst-reserved-prefix-okp tree rest)
             (lexeme-cst-literal-underscore-okp tree rest)
             (lexeme-cst-lifetime-quote-okp tree rest)
             (rv-spec-okp (cdr trees) rest)))))

(define rv-spec ((tests rv-test-listp) (n natp) (bad true-listp))
  :returns (mv (n-lexed natp :hyp (natp n))
               (bad-ids true-listp :hyp (true-listp bad)))
  :parents nil
  (if (endp tests)
      (mv n (revappend bad nil))
    (b* ((nats (rv-normalize (cdar tests)))
         (trees (lexemize-rust nats)))
      (cond ((reserrp trees) (rv-spec (cdr tests) n bad))
            ((rv-spec-okp trees nats) (rv-spec (cdr tests) (1+ n) bad))
            (t (rv-spec (cdr tests) (1+ n) (cons (caar tests) bad))))))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go-spec ((in stringp) state)
  :returns (mv summary state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       ((mv n bad) (rv-spec tests 0 nil)))
    (mv (list n bad) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Token boundaries: (rv-go-bounds in out state) writes, for each test,
; ("id" :err), ("id" :unbal), or ("id" (start . end) ...) with the
; code-point offsets of each token in the input (end exclusive),
; in edition 2024, the one that the Reference's rules correspond to.
; compare_bounds.py compares them with the tokens of the Reference's
; interpreter (reference-driver).  It returns the number of tests.

(define rv-bounds-aux ((trees abnf::tree-listp) (pos natp) (acc true-listp))
  :returns (bounds true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp trees)
      (revappend acc nil)
    (b* ((tree (car trees))
         (end (+ (lnfix pos) (len (abnf::tree->string tree))))
         (lexeme (abs-lexeme tree (rust::edition-2024))))
      (rv-bounds-aux (cdr trees)
                     end
                     (if (and (not (reserrp lexeme))
                              (equal (lexeme-kind lexeme) :token))
                         (cons (cons pos end) acc)
                       acc)))))

(define rv-bounds1 ((nats nat-listp))
  :parents nil
  (b* ((nats (rv-normalize nats))
       (trees (lexemize-rust nats))
       ((when (reserrp trees)) :err)
       (toks (tokenize-rust nats (rust::edition-2024) "t"))
       ((when (reserrp toks)) :err)
       ((when (reserrp (build-token-trees toks))) :unbal))
    (rv-bounds-aux trees 0 nil)))

(define rv-bounds ((tests rv-test-listp) (acc true-listp))
  :returns (results true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp tests)
      (revappend acc nil)
    (rv-bounds (cdr tests)
               (cons (cons (caar tests) (rv-bounds1 (cdar tests))) acc)))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go-bounds ((in stringp) (out stringp) state)
  :returns (mv (n natp) state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       (state (rv-write (rv-bounds tests nil) out state)))
    (mv (len tests) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The input layer: (rv-go-input in out edition state) reads the tests
; of input_format.py, in which the naturals of a test are
; the bytes of a whole file, and writes, for each test, ("id" x n),
; where n is the length of the shebang that the file starts with
; (0 if it starts with none, or if x is :utf8),
; and x is one of the following.
; - :utf8 if the bytes are not valid UTF-8.
; - :err if the lexer or tokenizer rejects the file.
; - :mismatched, :unclosed, or :unexpected if the token-tree builder
;   rejects the tokens of the file, with that kind of error.
; - :ok otherwise.
; It returns the number of tests.

(define rv-input1 ((bytes nat-listp) (edition rust::editionp))
  :parents nil
  (b* (((unless (byte-listp bytes)) (list :not-bytes 0))
       (stext (source-text-from-bytes bytes))
       ((when (reserrp stext)) (list :utf8 0))
       (shebang (shebang-length (source-text->text stext)))
       (toks (tokenize-source-text stext edition "t"))
       ((when (reserrp toks)) (list :err shebang))
       (trees (build-token-trees toks))
       ((when (reserrp trees)) (list (rv-delim-error trees) shebang)))
    (list :ok shebang)))

(define rv-input ((tests rv-test-listp)
                  (edition rust::editionp)
                  (acc true-listp))
  :returns (results true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp tests)
      (revappend acc nil)
    (rv-input (cdr tests)
              edition
              (cons (cons (caar tests) (rv-input1 (cdar tests) edition)) acc)))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go-input ((in stringp)
                     (out stringp)
                     (edition rust::editionp)
                     state)
  :returns (mv (n natp) state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       (state (rv-write (rv-input tests edition nil) out state)))
    (mv (len tests) state)))
