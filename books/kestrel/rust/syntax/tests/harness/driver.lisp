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
(include-book "../../extra-grammatical-restrictions")

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/file-io-light/write-objects-to-file" :dir :system)

; The ACL2 side of the differential tests of the lexer and tokenizer
; (see the xdoc topic differential-testing, and README.md in this directory).
; Each entry point reads a file of test inputs written by to_acl2.py,
; runs the lexer and tokenizer on each input,
; and writes a file of results, or returns a summary,
; for the comparison scripts in this directory.
; The functions are not in the manual (:parents nil):
; they are tools for testing, not part of the library.

(local (in-theory (enable abnf::tree-listp-when-result-not-error
                          lexemep-when-result-not-error
                          token+span-listp-when-result-not-error)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Counting tokens as the macros of run_rustc.py do.
; rustc turns an outer doc comment into the tokens of #[doc = "..."]
; and an inner one into those of #![doc = "..."].

; A count is a number, or :unbal if the delimiters do not match
; (rustc rejects those inputs while it builds token trees).

(define rv-countp (x)
  :returns (yes/no booleanp)
  :parents nil
  (or (natp x)
      (eq x :unbal)))

; Number of top-level token trees.

(define rv-tt-count ((tokens token+span-listp) (stack true-listp) (acc natp))
  :returns (count rv-countp
                  :hyp (natp acc)
                  :hints (("Goal" :in-theory (enable rv-countp))))
  :parents nil
  (b* (((when (endp tokens)) (if (endp stack) acc :unbal))
       (tok (token+span->token (car tokens)))
       (top (endp stack)))
    (token-case
     tok
     :open-delim (rv-tt-count (cdr tokens)
                              (cons tok.delim stack)
                              (if top (1+ acc) acc))
     :close-delim (if (and (consp stack) (equal (car stack) tok.delim))
                      (rv-tt-count (cdr tokens) (cdr stack) acc)
                    :unbal)
     :doc-comment (rv-tt-count
                   (cdr tokens)
                   stack
                   (if top
                       (+ acc (if (equal tok.style (doc-style-outer)) 2 3))
                     acc))
     :otherwise (rv-tt-count (cdr tokens) stack (if top (1+ acc) acc)))))

; Number of tokens at all depths, a delimited group counting as one
; plus its contents (the --deep count of run_rustc.py).

(define rv-deep-count ((tokens token+span-listp) (stack true-listp) (acc natp))
  :returns (count rv-countp
                  :hyp (natp acc)
                  :hints (("Goal" :in-theory (enable rv-countp))))
  :parents nil
  (b* (((when (endp tokens)) (if (endp stack) acc :unbal))
       (tok (token+span->token (car tokens))))
    (token-case
     tok
     :open-delim (rv-deep-count (cdr tokens) (cons tok.delim stack) (1+ acc))
     :close-delim (if (and (consp stack) (equal (car stack) tok.delim))
                      (rv-deep-count (cdr tokens) (cdr stack) acc)
                    :unbal)
     :doc-comment (rv-deep-count
                   (cdr tokens)
                   stack
                   (+ acc (if (equal tok.style (doc-style-outer)) 5 6)))
     :otherwise (rv-deep-count (cdr tokens) stack (1+ acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Short inputs: (rv-go in out edition state) writes, for each test,
; ("id" n) with the number of top-level token trees, ("id" :err) if
; the lexer or tokenizer rejects the input, or ("id" :unbal).
; It returns the number of tests.

(define rv-run1 ((nats nat-listp) (edition rust::editionp))
  :parents nil
  (b* ((toks (tokenize-rust nats edition "t")))
    (if (reserrp toks) :err (rv-tt-count toks nil 0))))

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

; Edition 2024 with a stand-in for the reserved guards, which the
; tokenizer does not implement yet: reject a "#" lexeme immediately
; followed by a lexeme that starts with "#" or a double quote.
; (rv-go-2024-guard in out state) is rv-go for edition 2024 plus this
; rule; it becomes redundant once the tokenizer has the rule.

(define rv-guard-flag ((trees abnf::tree-listp))
  :returns (yes/no booleanp)
  :parents nil
  (cond ((or (endp trees) (endp (cdr trees))) nil)
        ((and (equal (abnf::tree->string (car trees)) '(35))
              (b* ((next (abnf::tree->string (cadr trees))))
                (and (consp next)
                     (or (equal (car next) 35)
                         (equal (car next) 34)))))
         t)
        (t (rv-guard-flag (cdr trees)))))

(define rv-run1-2024-guard ((nats nat-listp))
  :parents nil
  (b* ((trees (lexemize-rust nats))
       ((when (reserrp trees)) :err)
       ((when (rv-guard-flag trees)) :err))
    (rv-run1 nats (rust::edition-2024))))

(define rv-run-2024-guard ((tests rv-test-listp) (acc true-listp))
  :returns (results true-listp :hyp (true-listp acc))
  :parents nil
  (if (endp tests)
      (revappend acc nil)
    (rv-run-2024-guard (cdr tests)
                       (cons (list (caar tests)
                                   (rv-run1-2024-guard (cdar tests)))
                             acc)))
  :guard-hints (("Goal" :in-theory (enable rv-testp))))

(define rv-go-2024-guard ((in stringp) (out stringp) state)
  :returns (mv (n natp) state)
  :parents nil
  (b* (((mv tests state) (rv-read-tests in state))
       (state (rv-write (rv-run-2024-guard tests nil) out state)))
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
  (b* (((mv & rest) (lex-*-lexeme nats))
       ((when (consp rest))
        (b* ((pos (nfix (- (len nats) (len rest)))))
          (list :lexerr
                (take (min 20 pos) (nthcdr (nfix (- pos 20)) nats))
                (take (min 30 (len rest)) rest))))
       (toks (tokenize-rust nats (rust::edition-2021) "t"))
       ((when (reserrp toks)) (list :tokerr)))
    (rv-deep-count toks nil 0)))

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
    (b* ((nats (cdar tests))
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
; in edition 2024 with the stand-in for the reserved guards.
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
  (b* ((trees (lexemize-rust nats))
       ((when (reserrp trees)) :err)
       ((when (rv-guard-flag trees)) :err)
       (toks (tokenize-rust nats (rust::edition-2024) "t"))
       ((when (reserrp toks)) :err)
       ((when (eq (rv-tt-count toks nil 0) :unbal)) :unbal))
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
