; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "post-parsing")
(include-book "syntax-abstraction")

(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "unicode/read-utf8" :dir :system)

(acl2::controlled-configuration :no-function nil)

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    acl2::nat-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser-interface
  :parents (parsing-and-printing)
  :short "API functions for parsing Remora source from a string."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are end-to-end entry points that take an ACL2 string of Remora
     source and return an "
    (xdoc::seetopic "abstract-syntax-trees" "abstract syntax tree (AST)")
    ".  Each is named @('parse-X-from-string'), where @('X') is a Remora
     grammar rule.  Internally each function calls a helper named
     @('parse-X-from-string-to-cst') (string &rarr; CST) and then applies the
     corresponding @(see syntax-abstraction) function to lift the CST to an
     AST.")
   (xdoc::p
    "The canonical entry points are @(tsee parse-from-string) (string &rarr;
     AST) and @(tsee parse-from-file) (file &rarr; AST), which parse a
     source file (imports followed by declarations) to a @(tsee file) AST.
     For standalone expressions &mdash; the input format of the
     implementation's @('interpret -e') and REPL &mdash; use
     @(tsee parse-top-exp-from-string) and
     @(tsee parse-top-exp-from-file).  The per-rule
     entries are retained for ongoing development and debugging, since they
     are useful for testing fragments of source in isolation.
     The per-rule entries currently cover @('ispace'), @('base-val'),
     @('base-type'), @('type-var'), @('ispace-var'), @('type'),
     @('char-lit'), @('string-lit'), @('exp'), @('atom'), and @('bind').")
   (xdoc::p
    "All entry points require the entire input to be consumed by the parse,
     and return a @(see reserr) on any failure (UTF-8 decode, parse, or
     abstraction).  ACL2 strings are sequences of bytes (char-codes 0-255);
     these entry points interpret those bytes as UTF-8 and decode them to
     Unicode code points before parsing.")
   (xdoc::p
    "The per-rule entry points and @(tsee ast-from-fragment) do "
    (xdoc::b "not")
    " enforce side condition [SC2] (keyword exclusion from identifiers).
     A fragment such as @('\"(let)\"') &mdash; which is not a well-formed
     @('let-exp') &mdash; will parse successfully under @(tsee
     parse-exp-from-string) as an @('app-exp') applying the identifier
     @('let') to no arguments, since the parser proper does not consult
     the keyword list.  Only the top-level entries
     (@(tsee parse-from-string) and @(tsee parse-from-file) for source
     files, @(tsee parse-top-exp-from-string) and
     @(tsee parse-top-exp-from-file) for standalone expressions, and
     their CST helpers @(tsee parse-file-from-codepoints) and
     @(tsee parse-top-exp-from-codepoints)) run the
     @(tsee check-tree-no-keyword-identifiers) walk that rejects
     keyword-named identifiers.  Consumers that need [SC2] enforcement
     on a fragment must apply it themselves; or, equivalently, route
     through the top-level entries and treat the fragment as the
     body of a standalone expression."))
  :order-subtopics t
  :default-parent t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Top-level-expression entry point for parsing to a CST.
;; For entry points for parsing to ASTs see the end of this file.
;;
;; parse-top-exp-from-codepoints is the CST-producing helper shared by
;; the user-facing AST entries.  It bundles the SC2 check from
;; post-parsing.lisp (xdoc topic post-parsing) into the parsing
;; pipeline (parse + [SC2] + input exhaustion).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-top-exp-from-codepoints ((codepoints nat-listp))
  :returns (tree abnf::tree-resultp)
  :hooks nil
  :short "Parse a standalone Remora expression
          from a list of Unicode code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the input as a @('top-exp')
     (an expression surrounded by optional whitespace),
     checks that all input is consumed,
     checks that the fringe of the output CST is equal to
     the input list of codepoints, and checks the extra-grammatical
     constraint [SC2] (no identifier may match a reserved keyword).
     Returns a @(tsee abnf::tree-resultp): a parse tree on success,
     or an error on failure."))
  (b* (((mv tree rest) (parse-top-exp codepoints))
       ((when (reserrp tree)) (reserrf-push tree))
       ((unless (null rest))
        (reserrf (cons :remaining-input rest)))
       ((unless (equal (abnf::tree->string tree)
                       codepoints))
        (reserrf (cons :fringe-mismatch
                       "internal parser bug -- please report this with the source that triggered it")))
       (check (check-tree-no-keyword-identifiers tree))
       ((when (reserrp check)) (reserrf-push check)))
    tree))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Supporting definitions that should be moved.

;; Conceptually, this would be nice if this definition were somewhere like
;;   books/unicode/utf8-decode.lisp
;; or in a new file in
;;   books/kestrel/unicode-light/
;; but since it uses define and string=>nats and acl2::nat-list-resultp
;; probably it would be better to put it in a new file like
;;   books/kestrel/utilities/strings/strings-unicodes.lisp

(define decode-utf8-string ((string stringp))
  :returns (codepoints acl2::nat-list-resultp)
  :short "Decode an ACL2 string interpreted as UTF-8 to a list of
          Unicode code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 strings are sequences of bytes (char-codes 0-255).  This helper
     interprets those bytes as a UTF-8 encoded sequence and decodes them
     to the corresponding Unicode code points.  Returns a @(see reserr)
     if the byte sequence is not valid UTF-8.")
   (xdoc::p
    "This is the bytes-to-code-points step shared by the
     string-input entry points."))
  (b* ((bytes (string=>nats (str-fix string)))
       ((unless (acl2::unsigned-byte-listp 8 bytes))
        (reserrf (cons :invalid-octets bytes)))
       (codepoints (acl2::utf8=>ustring bytes))
       ((unless (nat-listp codepoints))
        (reserrf (cons :invalid-utf-8 bytes))))
    codepoints))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Macros that drive the entry-point definitions.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; PARSE-TO-AST-AND-CHECK is an inline expansion of the full pipeline:
;; decode UTF-8, run parse-<rule-name>, check that the entire input was
;; consumed, then run abs-<rule-name>.  RULE-NAME is a symbol naming a
;; grammar rule for which both PARSE-<RULE-NAME> and ABS-<RULE-NAME> are
;; defined; SOURCE-STRING is an expression of type STRINGP.  At any
;; failure the expansion returns a RESERR.
;;
;; The literal symbol 'rule-name is used as the package witness for
;; packn-pos, ensuring the constructed names land in the REMORA package
;; even when the caller passes a rule symbol whose home package is
;; COMMON-LISP (e.g. CL::EXP, CL::ATOM).
(defmacro parse-to-ast-and-check (rule-name source-string)
  (b* ((parse-fn (acl2::packn-pos (list 'parse- rule-name) 'rule-name))
       (abs-fn   (acl2::packn-pos (list 'abs-   rule-name) 'rule-name)))
    `(b* ((codepoints (decode-utf8-string ,source-string))
          ((when (reserrp codepoints)) codepoints)
          ((mv tree rest) (,parse-fn codepoints))
          ((when (reserrp tree)) tree)
          ((unless (null rest))
           (reserrf (cons :remaining-input rest))))
       (,abs-fn tree))))

;; DEFPARSE-FROM-STRING generates two named entry points for a rule:
;;   (parse-<rule-name>-from-string-to-cst string) -> CST tree
;;   (parse-<rule-name>-from-string         string) -> AST result
;; RULE-NAME is the rule's symbol (used to find PARSE-<RULE-NAME> and
;; ABS-<RULE-NAME>); RESULT-PRED is the result predicate the AST entry
;; should advertise (e.g. ISPACE-RESULTP, KINDED-VAR-RESULTP).
;;
;; The literal symbol 'rule-name is used as the package witness for
;; packn-pos, ensuring the constructed names land in the REMORA package
;; even when the caller passes a rule symbol whose home package is
;; COMMON-LISP (e.g. CL::EXP, CL::ATOM).
(defmacro defparse-from-string (rule-name result-pred)
  (b* ((parse-fn  (acl2::packn-pos (list 'parse- rule-name) 'rule-name))
       (cst-fn    (acl2::packn-pos
                   (list 'parse- rule-name '-from-string-to-cst) 'rule-name))
       (ast-fn    (acl2::packn-pos
                   (list 'parse- rule-name '-from-string) 'rule-name))
       (rule-str  (acl2::string-downcase (symbol-name rule-name))))
    `(progn
       (define ,cst-fn ((string stringp))
         :returns (tree abnf::tree-resultp)
         :short ,(concatenate 'string
                              "Parse a @('" rule-str "') from a string to a CST.")
         (b* ((codepoints (decode-utf8-string string))
              ((when (reserrp codepoints)) codepoints)
              ((mv tree rest) (,parse-fn codepoints))
              ((when (reserrp tree)) tree)
              ((unless (null rest))
               (reserrf (cons :remaining-input rest))))
           tree))
       (define ,ast-fn ((string stringp))
         :returns (ast ,result-pred)
         :short ,(concatenate 'string
                              "Parse a @('" rule-str "') from a string to an AST.")
         (parse-to-ast-and-check ,rule-name string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Per-rule entry points (each generates two functions:
;;   parse-<rule>-from-string-to-cst  :: string -> CST
;;   parse-<rule>-from-string         :: string -> AST)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparse-from-string ispace      ispace-resultp)
(defparse-from-string base-val    base-lit-resultp)
(defparse-from-string base-type   base-type-resultp)
(defparse-from-string type-var    type-var-resultp)
(defparse-from-string ispace-var  ispace-var-resultp)
(defparse-from-string type    type-resultp)
(defparse-from-string char-lit    char-lit-resultp)
(defparse-from-string string-lit  char-lit-list-resultp)
(defparse-from-string exp         expr-resultp)
(defparse-from-string atom        atom-resultp)
(defparse-from-string bind        bind-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Generic fragment dispatcher
;; (convenient for testing)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ast-from-fragment ((rule-name stringp) (source-code stringp))
  :returns (ast (or (ispace-resultp ast)
                    (base-lit-resultp ast)
                    (base-type-resultp ast)
                    (type-var-resultp ast)
                    (ispace-var-resultp ast)
                    (type-resultp ast)
                    (char-lit-resultp ast)
                    (char-lit-list-resultp ast)
                    (expr-resultp ast)
                    (atom-resultp ast)
                    (bind-resultp ast)))
  :hooks nil
  :short "Parse and abstract a Remora source fragment to an AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Dispatches on @('rule-name'), which must be one of
     @('\"ispace\"'), @('\"base-val\"'), @('\"base-type\"'),
     @('\"type-var\"'), @('\"ispace-var\"'), @('\"type\"'),
     @('\"char-lit\"'), @('\"string-lit\"'), @('\"exp\"'),
     @('\"atom\"'), or @('\"bind\"').
     Other rule names produce a @(see reserr).")
   (xdoc::p
    "The result type is a disjunction over the AST result predicates of
     the supported rules.  As more rules become abstractable, both the
     dispatch and the result type grow accordingly."))
  (cond ((equal rule-name "ispace")
         (parse-to-ast-and-check ispace     source-code))
        ((equal rule-name "base-val")
         (parse-to-ast-and-check base-val   source-code))
        ((equal rule-name "base-type")
         (parse-to-ast-and-check base-type  source-code))
        ((equal rule-name "type-var")
         (parse-to-ast-and-check type-var   source-code))
        ((equal rule-name "ispace-var")
         (parse-to-ast-and-check ispace-var source-code))
        ((equal rule-name "type")
         (parse-to-ast-and-check type   source-code))
        ((equal rule-name "char-lit")
         (parse-to-ast-and-check char-lit   source-code))
        ((equal rule-name "string-lit")
         (parse-to-ast-and-check string-lit source-code))
        ((equal rule-name "exp")
         (parse-to-ast-and-check exp        source-code))
        ((equal rule-name "atom")
         (parse-to-ast-and-check atom       source-code))
        ((equal rule-name "bind")
         (parse-to-ast-and-check bind       source-code))
        (t (reserrf (cons :unsupported-rule-name rule-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Top-level-expression entry points for parsing to ASTs.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-top-exp-from-string ((string stringp))
  :returns (ast expr-resultp)
  :hooks nil
  :short "Parse a standalone Remora expression from an ACL2 string
          to an @(tsee expr) AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Treats @('string') as UTF-8 bytes (ACL2 strings are sequences of
     bytes with char-codes 0&ndash;255), decodes them to code points,
     composes @(tsee parse-top-exp-from-codepoints) to obtain a CST, then
     @(tsee abs-top-exp) to lift the CST to an @(tsee expr) AST.
     The full pipeline is UTF-8 decode + ABNF parse +
     [SC2] keyword check + input exhaustion + CST&rarr;AST abstraction.
     This is the analogue of the implementation's expression entry
     points (@('interpret -e') and the REPL); for source files see
     @(tsee parse-from-string)."))
  (b* (((okf codepoints) (decode-utf8-string string))
       ((okf tree) (parse-top-exp-from-codepoints codepoints)))
    (abs-top-exp tree)))

(define parse-top-exp-from-file ((filename stringp) state)
  :returns (mv (ast expr-resultp) state)
  :hooks nil
  :prepwork ((local (in-theory (disable acl2::read-utf8))))
  :short "Parse a standalone Remora expression from a file on disk
          to an @(tsee expr) AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads @('filename') as a UTF-8 file (using @('acl2::read-utf8')),
     composes @(tsee parse-top-exp-from-codepoints) to obtain a CST,
     then @(tsee abs-top-exp) to lift the CST to an @(tsee expr) AST.
     Relative paths are interpreted relative to the @('cbd').
     Returns @('(mv expr-resultp state)'): an AST on success, or
     an error on file-read / UTF-8 decode / parse / [SC2] / input
     exhaustion / abstraction failure.")
   (xdoc::p
    "@('acl2::read-utf8') returns either a @(tsee nat-listp) of
     code points (success) or an ACL2 string describing the failure.
     We dispatch on @(tsee nat-listp) to distinguish the cases."))
  (b* (((mv codepoints state)
        (acl2::read-utf8 (str-fix filename) state))
       ((unless (nat-listp codepoints))
        (mv (reserrf (cons :file-read-or-utf8-error codepoints))
            state))
       (tree (parse-top-exp-from-codepoints codepoints))
       ((when (reserrp tree))
        (mv tree state)))
    (mv (abs-top-exp tree) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; File-level entry points for parsing to ASTs.
;; These are the canonical entries for parsing Remora source.
;;
;; A `file` (grammar rule) is the contents of a .remora source file:
;; imports followed by declarations.  Like the top-exp entries
;; (and unlike the per-rule entries), these enforce the full pipeline:
;; UTF-8 decode + parse + [SC2] keyword check + input exhaustion +
;; CST->AST abstraction.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-file-from-codepoints ((codepoints nat-listp))
  :returns (tree abnf::tree-resultp)
  :hooks nil
  :short "Parse a Remora source file from a list of Unicode code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "File-level analogue of @(tsee parse-top-exp-from-codepoints):
     parses the input as a @('file') (imports followed by declarations),
     checks that all input is consumed,
     checks that the fringe of the output CST equals the input,
     and checks the extra-grammatical constraint [SC2]
     (no identifier may match a reserved keyword).
     Returns a @(tsee abnf::tree-resultp): a parse tree on success,
     or an error on failure."))
  (b* (((mv tree rest) (parse-file codepoints))
       ((when (reserrp tree)) (reserrf-push tree))
       ((unless (null rest))
        (reserrf (cons :remaining-input rest)))
       ((unless (equal (abnf::tree->string tree)
                       codepoints))
        (reserrf (cons :fringe-mismatch
                       "internal parser bug -- please report this with the source that triggered it")))
       (check (check-tree-no-keyword-identifiers tree))
       ((when (reserrp check)) (reserrf-push check)))
    tree))

(define parse-from-string ((string stringp))
  :returns (ast file-resultp)
  :hooks nil
  :short "Parse a Remora source file from an ACL2 string
          to a @(tsee file) AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Treats @('string') as UTF-8 bytes (ACL2 strings are sequences of
     bytes with char-codes 0&ndash;255), decodes them to code points,
     composes @(tsee parse-file-from-codepoints) to obtain a CST, then
     @(tsee abs-file) to lift the CST to a @(tsee file) AST.
     For standalone expressions see @(tsee parse-top-exp-from-string)."))
  (b* (((okf codepoints) (decode-utf8-string string))
       ((okf tree) (parse-file-from-codepoints codepoints)))
    (abs-file tree)))

(define parse-from-file ((filename stringp) state)
  :returns (mv (ast file-resultp) state)
  :hooks nil
  :prepwork ((local (in-theory (disable acl2::read-utf8))))
  :short "Parse a Remora source file from a file on disk
          to a @(tsee file) AST."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads @('filename') as a UTF-8 file (using @('acl2::read-utf8')),
     composes @(tsee parse-file-from-codepoints) to obtain a CST,
     then @(tsee abs-file) to lift the CST to a @(tsee file) AST.
     Relative paths are interpreted relative to the @('cbd')."))
  (b* (((mv codepoints state)
        (acl2::read-utf8 (str-fix filename) state))
       ((unless (nat-listp codepoints))
        (mv (reserrf (cons :file-read-or-utf8-error codepoints))
            state))
       (tree (parse-file-from-codepoints codepoints))
       ((when (reserrp tree))
        (mv tree state)))
    (mv (abs-file tree) state)))
