; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines recursive-descent parsers for C++ expressions, statements,
; block items, catch clauses, and the "full" variants of class member and
; class specifier parsing that handle inline method bodies.
;
; Compared to cpp-parser.lisp, this book adds:
;  - parse-cpp-expr               (full C++ expression: comma, assignment,
;                                  ternary, Pratt-style binary, prefix unary,
;                                  postfix chain, and primary)
;  - parse-cpp-block              (compound block: { block-items* })
;  - parse-cpp-block-item-list-body (statements/decls until '}')
;  - parse-cpp-block-item         (one block item: stmt or local declaration)
;  - parse-cpp-stmt               (one C++ statement)
;  - parse-cpp-catch-clause       (catch clause: header + body)
;  - parse-cpp-catch-clause-list  (zero or more catch clauses)
;  - parse-cpp-member-field-or-method-full
;                                 (like parse-cpp-member-field-or-method,
;                                  but parses an optional inline body)
;  - parse-cpp-member-decl-item-full
;  - parse-cpp-member-decl-list-body-full
;  - parse-cpp-class-specifier-full
;
; Limitations (constructs supported by the AST but not yet by the parser):
;  - lambda expressions with bodies (the AST :lambda variant is unused;
;    the parser does not recognize "[ ] ( ) { ... }")
;  - C++ named casts: static_cast<T>(e), dynamic_cast, reinterpret_cast,
;    const_cast, typeid
;  - C-style casts: (T)e (always parsed as parenthesized expr)
;  - new, delete expressions
;  - sizeof, alignof expressions
;  - try-catch statements (the parser produces a generic statement instead);
;    catch-clause parsing is still provided for use by ad-hoc clients
;  - for-decl, for-range (for-loop with declaration init or range-based)
;  - switch, case, default labels, goto labels
;  - co_await, co_yield, co_return prefix
;
; These limitations are tracked by leaving the corresponding AST variants
; reachable but not produced.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-parser")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cpp-expr-parser
  :parents (cpp-syntax)
  :short "Recursive-descent parser for C++ expressions, statements, and
          class member bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "This book extends @(see cpp-parser) with parsers for C++ expressions,
     statements, block items, catch clauses, and inline method bodies.
     It exposes both fine-grained entry points and \"full\" variants of the
     class-member and class-specifier parsers that allow inline bodies."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lambda capture list parser (standalone, before the mutual recursion block).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-one-capture ((parstate parstatep))
  :returns (mv erp
               (cap cpp-capture-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse one C++ lambda capture item."
  (b* (((reterr) (irr-cpp-capture) (irr-span) parstate)
       ((erp tok? tok-span parstate) (read-token parstate))
       ;; '=' -> default by-value
       ((when (token-punctuatorp tok? "="))
        (retok (cpp-capture-default-val) tok-span parstate))
       ;; '&' -> peek: if ident follows, by-ref named; else default-ref
       ((when (token-punctuatorp tok? "&"))
        (b* (((erp next? next-span parstate) (read-token parstate))
             ((when (and next? (token-case next? :ident)))
              (retok (make-cpp-capture-by-ref
                      :name (token-ident->ident next?))
                     (make-span :start (span->start tok-span)
                                :end   (span->end next-span))
                     parstate))
             ;; Not an ident -- put it back; this is default-ref [&]
             (parstate (if next? (unread-token parstate) parstate)))
          (retok (cpp-capture-default-ref) tok-span parstate)))
       ;; 'this' -> capture this
       ((when (token-keywordp tok? "this"))
        (retok (cpp-capture-this) tok-span parstate))
       ;; '*' followed by 'this' -> capture *this (C++17)
       ((when (token-punctuatorp tok? "*"))
        (b* (((erp this? this-span parstate) (read-token parstate))
             ((unless (token-keywordp this? "this"))
              (reterr-msg :where (span->start this-span)
                          :expected "'this' after '*' in capture list"
                          :found this?
                          :extra nil))
             (span (make-span :start (span->start tok-span)
                              :end   (span->end this-span))))
          (retok (cpp-capture-star-this) span parstate)))
       ;; identifier -> by-value capture
       ((when (and tok? (token-case tok? :ident)))
        (retok (make-cpp-capture-by-value
                :name (token-ident->ident tok?))
               tok-span parstate)))
    ;; Anything else is an error
    (reterr-msg :where (span->start tok-span)
                :expected "capture item ('=', '&', 'this', '*this', or identifier)"
                :found tok?
                :extra nil))
  ///
  (defret parsize-of-parse-cpp-one-capture-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token))))
  (defret parsize-of-parse-cpp-one-capture-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

(define parse-cpp-captures-rest ((acc cpp-capture-listp)
                                 (parstate parstatep))
  :returns (mv erp
               (captures cpp-capture-listp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :short "Parse remaining captures after the first, separated by commas."
  (b* (((reterr) nil parstate)
       ((erp tok? tok-span parstate) (read-token parstate))
       ;; ']' closes the capture list
       ((when (token-punctuatorp tok? "]"))
        (retok (cpp-capture-list-fix acc) parstate))
       ;; Must be ','
       ((unless (token-punctuatorp tok? ","))
        (reterr-msg :where (span->start tok-span)
                    :expected "',' or ']' in capture list"
                    :found tok?
                    :extra nil))
       ;; Parse next capture
       ((erp cap & parstate) (parse-cpp-one-capture parstate))
       ((erp rest parstate)
        (parse-cpp-captures-rest
         (append (cpp-capture-list-fix acc) (list cap)) parstate)))
    (retok rest parstate))
  ///
  (defret parsize-of-parse-cpp-captures-rest-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       parsize-of-parse-cpp-one-capture-uncond
                                       parsize-of-parse-cpp-one-capture-cond)))))

(define parse-cpp-capture-list ((parstate parstatep))
  :returns (mv erp
               (captures cpp-capture-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ lambda capture list @('[' captures @(']'))."
  (b* (((reterr) nil (irr-span) parstate)
       ((erp open? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open? "["))
        (reterr-msg :where (span->start open-span)
                    :expected "'[' to begin capture list"
                    :found open?
                    :extra nil))
       ;; Check for empty capture list '[]'
       ((erp peek? peek-span parstate) (read-token parstate))
       ((when (token-punctuatorp peek? "]"))
        (retok nil
               (make-span :start (span->start open-span)
                          :end   (span->end peek-span))
               parstate))
       ;; Non-empty: put back peek and parse first capture
       (parstate (if peek? (unread-token parstate) parstate))
       ((erp first & parstate) (parse-cpp-one-capture parstate))
       ;; Parse remaining captures (handles ',' cap ... ']')
       ((erp rest parstate)
        (parse-cpp-captures-rest (list first) parstate)))
    (retok rest
           (make-span :start (span->start open-span)
                      :end   (span->start open-span))
           parstate))
  ///
  (defret parsize-of-parse-cpp-capture-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-one-capture-uncond
                                       parsize-of-parse-cpp-captures-rest-uncond))))
  (defret parsize-of-parse-cpp-capture-list-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-one-capture-uncond
                                       parsize-of-parse-cpp-one-capture-cond
                                       parsize-of-parse-cpp-captures-rest-uncond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutual recursion for C++ expressions, statements, and lambda bodies
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ranks (lexicographic with parsize):
;   parse-cpp-primary             : rank 0
;   parse-cpp-postfix-rest        : rank 0
;   parse-cpp-unary               : rank 1
;   parse-cpp-pratt-loop          : rank 2
;   parse-cpp-cond-rest           : rank 3
;   parse-cpp-assign-or-cond      : rank 4
;   parse-cpp-expr                : rank 5
;   parse-cpp-arg-list-rest       : rank 6
;   parse-cpp-for-opt-test        : rank 6
;   parse-cpp-for-opt-next        : rank 6
;   parse-cpp-stmt                : rank 6
;   parse-cpp-block-item          : rank 7
;   parse-cpp-catch-clause        : rank 7
;   parse-cpp-block-item-list-body: rank 8
;   parse-cpp-catch-clause-list   : rank 8

(defines parse-cpp-full-mutual
  :parents (parser)

  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-unread-token
                                     parsize-of-parse-cpp-type-spec-uncond
                                     parsize-of-parse-cpp-type-spec-cond
                                     parsize-of-parse-cpp-type-spec-suffix-uncond
                                     parsize-of-parse-cpp-exception-handler-header-uncond
                                     parsize-of-parse-cpp-exception-handler-header-cond
                                     parsize-of-parse-cpp-param-list-uncond
                                     parsize-of-parse-cpp-param-list-cond
                                     parsize-of-parse-cpp-capture-list-uncond
                                     parsize-of-parse-cpp-capture-list-cond)))

  :ruler-extenders :all

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Primary expression
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-primary ((parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-expr) (irr-span) parstate)
         (psize-entry (parsize parstate))
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; this
         ((when (token-cpp-kw-p tok? "this"))
          (retok (cpp-expr-this) tok-span parstate))
         ;; identifier, possibly scoped (A::B::C)
         ;; Guard: skip C++ keyword identifiers that have dedicated cases below
         ;; (static_cast, dynamic_cast, reinterpret_cast, const_cast, typeid).
         ((when (and tok? (token-case tok? :ident)
                     (not (token-cpp-kw-p tok? "static_cast"))
                     (not (token-cpp-kw-p tok? "dynamic_cast"))
                     (not (token-cpp-kw-p tok? "reinterpret_cast"))
                     (not (token-cpp-kw-p tok? "const_cast"))
                     (not (token-cpp-kw-p tok? "typeid"))))
          (b* (((erp scope-tok? & parstate) (read-token parstate))
               ((when (token-punctuatorp scope-tok? "::"))
                (b* ((psize (parsize parstate))
                     ((erp inner inner-span parstate)
                      (parse-cpp-primary parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end inner-span))))
                  (retok (make-cpp-expr-scoped :scope (token-ident->ident tok?)
                                              :inner inner)
                         span parstate)))
               ;; Not '::' — put back
               (parstate (if scope-tok? (unread-token parstate) parstate)))
            (retok (make-cpp-expr-ident :name (token-ident->ident tok?))
                   tok-span parstate)))
         ;; constant
         ((when (and tok? (token-case tok? :const)))
          (retok (make-cpp-expr-const :value (c$::token-const->const tok?))
                 tok-span parstate))
         ;; string literal
         ((when (and tok? (token-case tok? :string)))
          (retok (make-cpp-expr-string
                  :value (list (c$::token-string->literal tok?)))
                 tok-span parstate))
         ;; parenthesized expression
         ((when (token-punctuatorp tok? "("))
          (b* ((psize (parsize parstate))
               ((erp inner & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp close? close-span parstate) (read-token parstate))
               ((unless (token-punctuatorp close? ")"))
                (reterr-msg :where (span->start close-span)
                            :expected "')' to close parenthesized expression"
                            :found close?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end close-span))))
            (retok (make-cpp-expr-paren :inner inner) span parstate)))
         ;; Lambda expression: '[' captures ']' '(' params ')' '{' body '}'
         ((when (token-punctuatorp tok? "["))
          (b* (;; tok-span is the span of '['; parstate is AFTER consuming '['.
               ;; capture-list-full takes open-span + post-'[' parstate (no unread needed).
               ((erp captures & parstate) (parse-cpp-capture-list-full tok-span parstate))
               ;; Ruler: capture-list-full doesn't increase parsize, so after
               ;; consuming '[' + captures we are still below entry parsize.
               ((unless (< (parsize parstate) psize-entry)) (reterr :impossible))
               ;; Parse parameter list '(' params ')'
               ((erp params & parstate) (parse-cpp-param-list parstate))
               ;; Record parsize before consuming '{'
               (psize-lambda (parsize parstate))
               ;; Read '{'
               ((erp lbrace? lbrace-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lbrace? "{"))
                (reterr-msg :where (span->start lbrace-span)
                            :expected "'{' to begin lambda body"
                            :found lbrace?
                            :extra nil))
               ;; Strict parsize decrease after consuming '{'
               ((unless (mbt (< (parsize parstate) psize-lambda)))
                (reterr :impossible))
               ;; Parse body items (until '}')
               ((erp body & parstate) (parse-cpp-block-item-list-body parstate))
               ;; Read '}'
               ((erp rbrace? rbrace-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rbrace? "}"))
                (reterr-msg :where (span->start rbrace-span)
                            :expected "'}' to close lambda body"
                            :found rbrace?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rbrace-span))))
            (retok (make-cpp-expr-lambda
                    :captures captures
                    :params   params
                    :body     body)
                   span parstate)))
         ;; C++ named cast: static_cast<T>(e)
         ((when (token-cpp-kw-p tok? "static_cast"))
          (b* (((erp lt? lt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lt? "<"))
                (reterr-msg :where (span->start lt-span)
                            :expected "'<' after 'static_cast'"
                            :found lt?
                            :extra nil))
               (psize (parsize parstate))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp gt? gt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp gt? ">"))
                (reterr-msg :where (span->start gt-span)
                            :expected "'>' after type in static_cast"
                            :found gt?
                            :extra nil))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'static_cast<T>'"
                            :found lp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp arg & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after cast expression"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-static-cast :type type :arg arg)
                   span parstate)))
         ;; dynamic_cast<T>(e)
         ((when (token-cpp-kw-p tok? "dynamic_cast"))
          (b* (((erp lt? lt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lt? "<"))
                (reterr-msg :where (span->start lt-span)
                            :expected "'<' after 'dynamic_cast'"
                            :found lt?
                            :extra nil))
               (psize (parsize parstate))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp gt? gt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp gt? ">"))
                (reterr-msg :where (span->start gt-span)
                            :expected "'>' after type in dynamic_cast"
                            :found gt?
                            :extra nil))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'dynamic_cast<T>'"
                            :found lp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp arg & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after cast expression"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-dynamic-cast :type type :arg arg)
                   span parstate)))
         ;; reinterpret_cast<T>(e)
         ((when (token-cpp-kw-p tok? "reinterpret_cast"))
          (b* (((erp lt? lt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lt? "<"))
                (reterr-msg :where (span->start lt-span)
                            :expected "'<' after 'reinterpret_cast'"
                            :found lt?
                            :extra nil))
               (psize (parsize parstate))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp gt? gt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp gt? ">"))
                (reterr-msg :where (span->start gt-span)
                            :expected "'>' after type in reinterpret_cast"
                            :found gt?
                            :extra nil))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'reinterpret_cast<T>'"
                            :found lp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp arg & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after cast expression"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-reinterpret-cast :type type :arg arg)
                   span parstate)))
         ;; const_cast<T>(e)
         ((when (token-cpp-kw-p tok? "const_cast"))
          (b* (((erp lt? lt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lt? "<"))
                (reterr-msg :where (span->start lt-span)
                            :expected "'<' after 'const_cast'"
                            :found lt?
                            :extra nil))
               (psize (parsize parstate))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp gt? gt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp gt? ">"))
                (reterr-msg :where (span->start gt-span)
                            :expected "'>' after type in const_cast"
                            :found gt?
                            :extra nil))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'const_cast<T>'"
                            :found lp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp arg & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after cast expression"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-const-cast :type type :arg arg)
                   span parstate)))
         ;; typeid(T) or typeid(expr) — disambiguate by peeking after '('
         ;; Heuristic (same as sizeof): keyword => type; ident+ident => type; else expr.
         ((when (token-cpp-kw-p tok? "typeid"))
          (b* (;; psize captures parsize AFTER tok? was consumed, BEFORE reading lp?.
               ;; After consuming lp? and peeking+unreading inner?, parsize = psize-1,
               ;; satisfying the guard for the upward-rank call to parse-cpp-assign-or-cond.
               (psize (parsize parstate))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'typeid'"
                            :found lp?
                            :extra nil))
               ;; Peek inside '(' to decide: type form vs expression form.
               ((erp inner? & parstate) (read-token parstate))
               ((mv type-first-p parstate)
                (if (or (and inner? (token-case inner? :keyword))
                        (token-keywordp inner? "const")
                        (token-keywordp inner? "volatile"))
                    ;; C17 keyword — definitely a type specifier
                    (b* ((parstate (if inner? (unread-token parstate) parstate)))
                      (mv t parstate))
                  (if (and inner? (token-case inner? :ident))
                      ;; Single ident: peek one more — ident ident => type (typedef + var)
                      (b* (((mv erp2 inner2? & parstate) (read-token parstate))
                           (two-ident-p (and (not erp2)
                                            inner2?
                                            (token-case inner2? :ident)))
                           (parstate (if (and (not erp2) inner2?)
                                        (unread-token parstate)
                                      parstate))
                           (parstate (if inner? (unread-token parstate) parstate)))
                        (mv two-ident-p parstate))
                    ;; Not keyword or ident — expression form
                    (b* ((parstate (if inner? (unread-token parstate) parstate)))
                      (mv nil parstate)))))
               ((when type-first-p)
                ;; typeid(T): parse a full type spec then ')'
                (b* (((erp type & parstate) (parse-cpp-type-spec-full parstate))
                     ((erp rp? rp-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp rp? ")"))
                      (reterr-msg :where (span->start rp-span)
                                  :expected "')' after type in typeid"
                                  :found rp?
                                  :extra nil))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end rp-span))))
                  (retok (make-cpp-expr-typeid-type :type type) span parstate)))
               ;; typeid(expr): parsize is now < psize (consumed 'typeid' + '(').
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp arg & parstate) (parse-cpp-assign-or-cond parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after expression in typeid"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-typeid-expr :arg arg) span parstate))))
      (reterr-msg :where (span->start tok-span)
                  :expected "primary expression"
                  :found tok?
                  :extra nil)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Argument list rest: parses arguments inside '(' ... ')' or after ','.
  ;; Caller has consumed '(' (or ',') so first call has parsize already
  ;; decreased.  Returns the accumulated reversed-argument list and the
  ;; span of the closing ')'.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-arg-list-rest ((acc cpp-expr-listp) (parstate parstatep))
    :returns (mv erp
                 (args cpp-expr-listp)
                 (close-span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 6)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         ;; Peek: empty '()' or next arg
         ((erp tok? tok-span parstate) (read-token parstate))
         ((when (token-punctuatorp tok? ")"))
          (retok (cpp-expr-list-fix acc) tok-span parstate))
         ;; EOF without ')' is an error
         ((unless tok?)
          (reterr-msg :where (span->start tok-span)
                      :expected "expression or ')' in argument list"
                      :found nil
                      :extra nil))
         (parstate (unread-token parstate))
         ;; Parse one arg (assignment-expression, not full comma-expression)
         (psize (parsize parstate))
         ((erp arg & parstate) (parse-cpp-assign-or-cond parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Read separator
         ((erp sep? sep-span parstate) (read-token parstate))
         ((when (token-punctuatorp sep? ")"))
          (retok (append (cpp-expr-list-fix acc) (list arg))
                 sep-span parstate))
         ((unless (token-punctuatorp sep? ","))
          (reterr-msg :where (span->start sep-span)
                      :expected "',' or ')' in argument list"
                      :found sep?
                      :extra nil))
         ((erp rest close-span parstate)
          (parse-cpp-arg-list-rest
           (append (cpp-expr-list-fix acc) (list arg)) parstate)))
      (retok rest close-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Postfix-rest: takes an already-parsed primary as lhs, builds a chain
  ;; of postfix operations: '.', '->', '[]', '()', '++', '--'.
  ;; Stops when the next token is not a postfix operator.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-postfix-rest ((lhs cpp-expr-p)
                                  (lhs-span spanp)
                                  (parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (b* (((reterr) (cpp-expr-fix lhs) (c$::span-fix lhs-span) parstate)
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; '.' member or '.*' pointer-to-member
         ((when (token-punctuatorp tok? "."))
          (b* (((erp next? next-span parstate) (read-token parstate))
               ;; '.*' pointer-to-member dereference
               ((when (token-punctuatorp next? "*"))
                (b* ((psize (parsize parstate))
                     ((erp rhs rhs-span parstate) (parse-cpp-unary parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start lhs-span)
                                      :end   (span->end rhs-span)))
                     (new-lhs (make-cpp-expr-dot-star :lhs lhs :rhs rhs)))
                  (parse-cpp-postfix-rest new-lhs span parstate)))
               ;; '.' ident member access
               ((unless (and next? (token-case next? :ident)))
                (reterr-msg :where (span->start next-span)
                            :expected "identifier or '*' after '.'"
                            :found next?
                            :extra nil))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end next-span)))
               (new-lhs (make-cpp-expr-member
                         :object lhs
                         :name (token-ident->ident next?))))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '->' member-pointer or '->*' pointer-to-member via pointer
         ((when (token-punctuatorp tok? "->"))
          (b* (((erp next? next-span parstate) (read-token parstate))
               ;; '->*' pointer-to-member dereference via pointer
               ((when (token-punctuatorp next? "*"))
                (b* ((psize (parsize parstate))
                     ((erp rhs rhs-span parstate) (parse-cpp-unary parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start lhs-span)
                                      :end   (span->end rhs-span)))
                     (new-lhs (make-cpp-expr-arrow-star :lhs lhs :rhs rhs)))
                  (parse-cpp-postfix-rest new-lhs span parstate)))
               ;; '->' ident member access via pointer
               ((unless (and next? (token-case next? :ident)))
                (reterr-msg :where (span->start next-span)
                            :expected "identifier or '*' after '->'"
                            :found next?
                            :extra nil))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end next-span)))
               (new-lhs (make-cpp-expr-memberp
                         :object lhs
                         :name (token-ident->ident next?))))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '[' subscript
         ((when (token-punctuatorp tok? "["))
          (b* ((psize (parsize parstate))
               ((erp idx & parstate) (parse-cpp-expr parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp close? close-span parstate) (read-token parstate))
               ((unless (token-punctuatorp close? "]"))
                (reterr-msg :where (span->start close-span)
                            :expected "']' to close subscript"
                            :found close?
                            :extra nil))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end close-span)))
               (new-lhs (make-cpp-expr-arrsub :array lhs :index idx)))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '(' function call
         ((when (token-punctuatorp tok? "("))
          (b* ((psize (parsize parstate))
               ((erp args close-span parstate)
                (parse-cpp-arg-list-rest nil parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end close-span)))
               (new-lhs (make-cpp-expr-call :fun lhs :args args)))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '++' post-increment
         ((when (token-punctuatorp tok? "++"))
          (b* ((span (make-span :start (span->start lhs-span)
                                :end   (span->end tok-span)))
               (new-lhs (make-cpp-expr-postinc :arg lhs)))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '--' post-decrement
         ((when (token-punctuatorp tok? "--"))
          (b* ((span (make-span :start (span->start lhs-span)
                                :end   (span->end tok-span)))
               (new-lhs (make-cpp-expr-postdec :arg lhs)))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; Not a postfix operator — put token back and return lhs
         (parstate (if tok? (unread-token parstate) parstate)))
      (retok (cpp-expr-fix lhs) (c$::span-fix lhs-span) parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Unary expression: optional prefix operator(s), then postfix chain.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-unary ((parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 1)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-expr) (irr-span) parstate)
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; '++' prefix
         ((when (token-punctuatorp tok? "++"))
          (b* ((psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-preinc :arg sub) span parstate)))
         ;; '--' prefix
         ((when (token-punctuatorp tok? "--"))
          (b* ((psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-predec :arg sub) span parstate)))
         ;; Simple unary operator: + - ! ~ * &
         ((when (token-cpp-prefix-unop-p tok?))
          (b* ((op (token-to-cpp-prefix-unop tok?))
               (psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-unary :op op :arg sub) span parstate)))
         ;; 'throw' with optional expression
         ((when (token-cpp-kw-p tok? "throw"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ;; If next is ',' ';' ')' or end, this is bare throw (rethrow)
               ((when (or (not peek?)
                          (token-punctuatorp peek? ";")
                          (token-punctuatorp peek? ",")
                          (token-punctuatorp peek? ")")))
                (b* ((parstate (if peek? (unread-token parstate) parstate)))
                  (retok (cpp-expr-rethrow) tok-span parstate)))
               (parstate (unread-token parstate))
               (psize (parsize parstate))
               ((erp sub sub-span parstate)
                (parse-cpp-assign-or-cond parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-throw-expr :arg sub) span parstate)))
         ;; 'sizeof' expr  or  'sizeof' '(' T ')'
         ((when (token-keywordp tok? "sizeof"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ;; '(' — could be sizeof(T) or sizeof(expr)
               ((when (token-punctuatorp peek? "("))
                (b* (;; Peek one more token to decide: type keyword or ident?
                     ((erp inner? & parstate) (read-token parstate))
                     ((mv type-first-p parstate)
                      (if (or (and inner? (token-case inner? :keyword))
                              (token-keywordp inner? "const")
                              (token-keywordp inner? "volatile"))
                          ;; Looks like a type: put inner? back and parse type
                          (b* ((parstate
                                (if inner? (unread-token parstate) parstate)))
                            (mv t parstate))
                        ;; If ident, peek one more to check for ident ident
                        (if (and inner? (token-case inner? :ident))
                            (b* (((mv erp2 inner2? & parstate)
                                  (read-token parstate))
                                 (two-ident-p
                                  (and (not erp2)
                                       inner2?
                                       (token-case inner2? :ident)))
                                 ;; Put inner2? back
                                 (parstate
                                  (if (and (not erp2) inner2?)
                                      (unread-token parstate)
                                    parstate))
                                 ;; Put inner? back
                                 (parstate
                                  (if inner? (unread-token parstate) parstate)))
                              (mv two-ident-p parstate))
                          ;; Not a keyword or ident: expression form
                          (b* ((parstate
                                (if inner? (unread-token parstate) parstate)))
                            (mv nil parstate)))))
                     ((when type-first-p)
                      ;; sizeof(T): parse type inside parens
                      (b* (((erp type & parstate) (parse-cpp-type-spec-full parstate))
                           ((erp rp? rp-span parstate) (read-token parstate))
                           ((unless (token-punctuatorp rp? ")"))
                            (reterr-msg :where (span->start rp-span)
                                        :expected "')' after type in sizeof"
                                        :found rp?
                                        :extra nil))
                           (span (make-span :start (span->start tok-span)
                                            :end   (span->end rp-span))))
                        (retok (make-cpp-expr-sizeof-type :type type)
                               span parstate)))
                     ;; sizeof(expr): peek? = '(' already consumed;
                     ;; parsize is strictly less than entry.
                     (psize (parsize parstate))
                     ((erp sub sub-span parstate) (parse-cpp-unary parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end sub-span))))
                  (retok (make-cpp-expr-sizeof-expr :arg sub) span parstate)))
               ;; sizeof expr (no parens): put peek? back and parse unary
               (parstate (if peek? (unread-token parstate) parstate))
               (psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-sizeof-expr :arg sub) span parstate)))
         ;; 'alignof' '(' T ')'
         ((when (token-cpp-kw-p tok? "alignof"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'alignof'"
                            :found lp?
                            :extra nil))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after type in alignof"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-alignof-type :type type) span parstate)))
         ;; 'new' T [ '(' args ')' ]
         ((when (token-cpp-kw-p tok? "new"))
          (b* ((psize-new (parsize parstate))
               ((erp type type-span parstate) (parse-cpp-type-spec-full parstate))
               ((erp peek? & parstate) (read-token parstate))
               ((when (token-punctuatorp peek? "("))
                (b* ((psize (parsize parstate))
                     ((unless (< (parsize parstate) psize-new))
                      (reterr :impossible))
                     ((erp args close-span parstate)
                      (parse-cpp-arg-list-rest nil parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end close-span))))
                  (retok (make-cpp-expr-new :type type :args args)
                         span parstate)))
               (parstate (if peek? (unread-token parstate) parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end type-span))))
            (retok (make-cpp-expr-new :type type :args nil) span parstate)))
         ;; 'delete' [ '[' ']' ] expr
         ((when (token-cpp-kw-p tok? "delete"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ((mv arrayp parstate)
                (if (token-punctuatorp peek? "[")
                    (b* (((mv erp-rb rb? & parstate) (read-token parstate)))
                      (if (and (not erp-rb) (token-punctuatorp rb? "]"))
                          (mv t parstate)
                        ;; Not '[]': put rb? back (if non-error) then put '[' back
                        (b* ((parstate (if (and (not erp-rb) rb?)
                                          (unread-token parstate)
                                        parstate))
                             (parstate (unread-token parstate)))
                          (mv nil parstate))))
                  (b* ((parstate (if peek? (unread-token parstate) parstate)))
                    (mv nil parstate))))
               (psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-delete :arg sub :arrayp arrayp)
                   span parstate)))
         ;; 'co_await' expr
         ((when (token-cpp-kw-p tok? "co_await"))
          (b* ((psize (parsize parstate))
               ((erp sub sub-span parstate) (parse-cpp-unary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end sub-span))))
            (retok (make-cpp-expr-co-await :arg sub) span parstate)))
         ;; C-style cast: '(' type ')' cast-expr
         ;; Intercept '(' before falling through to primary.
         ((when (token-punctuatorp tok? "("))
          (b* (((erp inner? & parstate) (read-token parstate))
               ;; Case 1: C keyword type -> definitely a cast
               ((when (and inner? (token-case inner? :keyword)))
                (b* ((psize-term (parsize parstate))
                     (parstate (unread-token parstate))
                     ((erp type & parstate) (parse-cpp-type-spec-full parstate))
                     ((erp rp? rp-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp rp? ")"))
                      (reterr-msg :where (span->start rp-span)
                                  :expected "')' after cast type"
                                  :found rp?
                                  :extra nil))
                     ((unless (< (parsize parstate) psize-term))
                      (reterr :impossible))
                     ((erp arg arg-span parstate) (parse-cpp-unary parstate))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end arg-span))))
                  (retok (make-cpp-expr-c-cast :type type :arg arg)
                         span parstate)))
               ;; Case 2: single ident followed by ')' then primary-start -> cast
               ((when (and inner? (token-case inner? :ident)))
                (b* (((erp after? & parstate) (read-token parstate))
                     ((unless (token-punctuatorp after? ")"))
                      (b* ((parstate (if after? (unread-token parstate) parstate))
                           (parstate (unread-token parstate)) ; ident
                           (parstate (unread-token parstate)) ; '('
                           (psize (parsize parstate))
                           ((erp prim prim-span parstate) (parse-cpp-primary parstate))
                           ((unless (mbt (<= (parsize parstate) psize)))
                            (reterr :impossible)))
                        (parse-cpp-postfix-rest prim prim-span parstate)))
                     ((erp next? & parstate) (read-token parstate))
                     (is-cast-context
                      (or (and next? (token-case next? :ident))
                          (and next? (token-case next? :const))
                          (and next? (token-case next? :string))
                          (token-punctuatorp next? "(")
                          (token-punctuatorp next? "++")
                          (token-punctuatorp next? "--")
                          (token-punctuatorp next? "~")
                          (token-punctuatorp next? "!")
                          (token-punctuatorp next? "-")
                          (token-punctuatorp next? "+")
                          (token-punctuatorp next? "*")
                          (token-punctuatorp next? "&")))
                     ((unless is-cast-context)
                      (b* ((parstate (if next? (unread-token parstate) parstate))
                           (parstate (unread-token parstate)) ; ')'
                           (parstate (unread-token parstate)) ; ident
                           (parstate (unread-token parstate)) ; '('
                           (psize (parsize parstate))
                           ((erp prim prim-span parstate) (parse-cpp-primary parstate))
                           ((unless (mbt (<= (parsize parstate) psize)))
                            (reterr :impossible)))
                        (parse-cpp-postfix-rest prim prim-span parstate)))
                     (parstate (if next? (unread-token parstate) parstate))
                     (type (make-cpp-type-spec-name :id (token-ident->ident inner?)))
                     (psize (parsize parstate))
                     ((erp arg arg-span parstate) (parse-cpp-unary parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end arg-span))))
                  (retok (make-cpp-expr-c-cast :type type :arg arg)
                         span parstate)))
               ;; inner? is neither keyword nor ident -> fall through to primary
               (parstate (if inner? (unread-token parstate) parstate))
               (parstate (unread-token parstate)) ; put '(' back
               (psize (parsize parstate))
               ((erp prim prim-span parstate) (parse-cpp-primary parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible)))
            (parse-cpp-postfix-rest prim prim-span parstate)))
         ;; Otherwise: not a unary prefix -- primary followed by postfix
         ((unless tok?)
          (reterr-msg :where (span->start tok-span)
                      :expected "primary expression"
                      :found nil
                      :extra nil))
         (parstate (unread-token parstate))
         (psize (parsize parstate))
         ((erp prim prim-span parstate) (parse-cpp-primary parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible)))
      (parse-cpp-postfix-rest prim prim-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Pratt loop for binary operators at precedence levels 4..13.
  ;; Consumes a sequence of "op rhs" while op-precedence >= min-prec.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-pratt-loop ((min-prec natp)
                                (lhs cpp-expr-p)
                                (lhs-span spanp)
                                (parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 2)
    :verify-guards nil
    (b* (((reterr) (cpp-expr-fix lhs) (c$::span-fix lhs-span) parstate)
         ((erp op? & parstate) (read-token parstate))
         ;; No token (EOF): stop.
         ((unless op?)
          (retok (cpp-expr-fix lhs) (c$::span-fix lhs-span) parstate))
         (p (token-to-cpp-infix-prec op?))
         ;; If op-prec is out of [max(min-prec,4)..13], stop.
         ((when (or (< p (acl2::lnfix min-prec))
                    (< p 4)
                    (> p 13)))
          (b* ((parstate (unread-token parstate)))
            (retok (cpp-expr-fix lhs) (c$::span-fix lhs-span) parstate)))
         ;; Consume the operator (already consumed above) and parse RHS
         (psize (parsize parstate))
         ((erp rhs rhs-span parstate) (parse-cpp-unary parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Climb: greedy on higher-precedence operators
         (next-min (+ p 1))
         ((erp rhs rhs-span parstate)
          (parse-cpp-pratt-loop next-min rhs rhs-span parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Build the binop
         (binop (token-to-cpp-infix-binop op?))
         (new-lhs (make-cpp-expr-binary :op binop :lhs lhs :rhs rhs))
         (new-span (make-span :start (span->start lhs-span)
                              :end   (span->end rhs-span))))
      (parse-cpp-pratt-loop (acl2::lnfix min-prec) new-lhs new-span parstate))
    :guard-hints
    (("Goal" :in-theory (enable token-to-cpp-infix-prec))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Ternary tail: caller has parsed the test; we still need to consume
  ;; '?' here (so that subsequent calls into parse-cpp-expr happen with a
  ;; strictly smaller parsize than this function's entry parsize, ensuring
  ;; the lexicographic measure decreases).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-cond-rest ((test cpp-expr-p)
                               (test-span spanp)
                               (parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 3)
    :verify-guards nil
    (b* (((reterr) (cpp-expr-fix test) (c$::span-fix test-span) parstate)
         ((erp q? q-span parstate) (read-token parstate))
         ((unless (token-punctuatorp q? "?"))
          (reterr-msg :where (span->start q-span)
                      :expected "'?' in ternary expression"
                      :found q?
                      :extra nil))
         (psize (parsize parstate))
         ((erp then & parstate) (parse-cpp-expr parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ((erp colon? colon-span parstate) (read-token parstate))
         ((unless (token-punctuatorp colon? ":"))
          (reterr-msg :where (span->start colon-span)
                      :expected "':' in ternary expression"
                      :found colon?
                      :extra nil))
         ((erp else else-span parstate) (parse-cpp-assign-or-cond parstate))
         (span (make-span :start (span->start test-span)
                          :end   (span->end else-span))))
      (retok (make-cpp-expr-cond :test test :then then :else else)
             span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Assignment-or-conditional expression (no comma).
  ;;   1. parse unary
  ;;   2. peek; if assignment op, recurse (right-assoc)
  ;;   3. else run Pratt loop; if then '?' follow with ternary tail
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-assign-or-cond ((parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 4)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp lhs lhs-span parstate) (parse-cpp-unary parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ((erp op? & parstate) (read-token parstate))
         ;; If no token (EOF), no operator possible — return lhs as-is.
         ((unless op?)
          (retok lhs lhs-span parstate))
         (p (token-to-cpp-infix-prec op?))
         ;; Assignment: right-associative
         ((when (equal p 2))
          (b* ((aop (token-to-cpp-assign-op op?))
               ((erp rhs rhs-span parstate)
                (parse-cpp-assign-or-cond parstate))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end rhs-span))))
            (retok (make-cpp-expr-assign :op aop :lhs lhs :rhs rhs)
                   span parstate)))
         ;; Put back the (non-assignment) token before running Pratt
         (parstate (unread-token parstate))
         ;; Run Pratt loop for binary operators (precedence 4..13)
         ((erp pratt-expr pratt-span parstate)
          (parse-cpp-pratt-loop 4 lhs lhs-span parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Check for ternary '?'  (cond-rest will consume the '?' itself)
         ((erp q? & parstate) (read-token parstate))
         ((unless (token-punctuatorp q? "?"))
          (b* ((parstate (if q? (unread-token parstate) parstate)))
            (retok pratt-expr pratt-span parstate)))
         (parstate (unread-token parstate)))
      (parse-cpp-cond-rest pratt-expr pratt-span parstate))
    :guard-hints
    (("Goal" :in-theory (enable token-to-cpp-infix-prec))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Top-level C++ expression: parses an assignment-expression, then handles
  ;; comma operators (left-associative).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-expr ((parstate parstatep))
    :returns (mv erp
                 (expr cpp-expr-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 5)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-expr) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp lhs lhs-span parstate) (parse-cpp-assign-or-cond parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ((erp comma? & parstate) (read-token parstate))
         ((unless (token-punctuatorp comma? ","))
          (b* ((parstate (if comma? (unread-token parstate) parstate)))
            (retok lhs lhs-span parstate)))
         ((erp rhs rhs-span parstate) (parse-cpp-expr parstate))
         (span (make-span :start (span->start lhs-span)
                          :end   (span->end rhs-span))))
      (retok (make-cpp-expr-comma :lhs lhs :rhs rhs) span parstate)))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; For-loop helper: parse optional expression followed by ';'
  ;; Rank 6 (calls parse-cpp-expr at rank 5 after unread).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-for-opt-test ((parstate parstatep))
    :returns (mv erp
                 (present-p booleanp)
                 (expr cpp-expr-p)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 6)
    :verify-guards nil
    :short "Parse an optional C++ for-loop test expression followed by @(';')."
    (b* (((reterr) nil (irr-cpp-expr) parstate)
         ((erp t1? t1-span parstate) (read-token parstate))
         ;; Empty: first token is ';'
         ((when (token-punctuatorp t1? ";"))
          (retok nil (irr-cpp-expr) parstate))
         ;; EOF before ';': error
         ((unless t1?)
          (reterr-msg :where (span->start t1-span)
                      :expected "expression or ';' in for-loop"
                      :found nil
                      :extra nil))
         ;; Non-empty: put t1? back and parse expression
         (parstate (unread-token parstate))
         ((erp te & parstate) (parse-cpp-expr parstate))
         ((erp semi? semi-span parstate) (read-token parstate))
         ((unless (token-punctuatorp semi? ";"))
          (reterr-msg :where (span->start semi-span)
                      :expected "';' after for-loop expression"
                      :found semi?
                      :extra nil)))
      (retok t te parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; For-loop helper: parse optional expression followed by ')'
  ;; Rank 6 (calls parse-cpp-expr at rank 5 after unread).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-for-opt-next ((parstate parstatep))
    :returns (mv erp
                 (present-p booleanp)
                 (expr cpp-expr-p)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 6)
    :verify-guards nil
    :short "Parse an optional C++ for-loop next expression followed by @(')')."
    (b* (((reterr) nil (irr-cpp-expr) parstate)
         ((erp n1? n1-span parstate) (read-token parstate))
         ;; Empty: first token is ')'
         ((when (token-punctuatorp n1? ")"))
          (retok nil (irr-cpp-expr) parstate))
         ;; EOF before ')': error
         ((unless n1?)
          (reterr-msg :where (span->start n1-span)
                      :expected "expression or ')' in for-loop"
                      :found nil
                      :extra nil))
         ;; Non-empty: put n1? back and parse expression
         (parstate (unread-token parstate))
         ((erp ne & parstate) (parse-cpp-expr parstate))
         ((erp rp? rp-span parstate) (read-token parstate))
         ((unless (token-punctuatorp rp? ")"))
          (reterr-msg :where (span->start rp-span)
                      :expected "')' after for-loop next expression"
                      :found rp?
                      :extra nil)))
      (retok t ne parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse one C++ statement.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-stmt ((parstate parstatep))
    :returns (mv erp
                 (stmt cpp-stmt-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 6)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-stmt) (irr-span) parstate)
         (psize (parsize parstate))
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; ';' empty statement
         ((when (token-punctuatorp tok? ";"))
          (retok (cpp-stmt-expr-void) tok-span parstate))
         ;; '{' compound statement
         ((when (token-punctuatorp tok? "{"))
          (b* (((erp items & parstate)
                (parse-cpp-block-item-list-body parstate))
               ((erp close? close-span parstate) (read-token parstate))
               ((unless (token-punctuatorp close? "}"))
                (reterr-msg :where (span->start close-span)
                            :expected "'}' to close compound statement"
                            :found close?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end close-span))))
            (retok (make-cpp-stmt-compound :body items) span parstate)))
         ;; 'return' statement
         ((when (token-keywordp tok? "return"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ((when (token-punctuatorp peek? ";"))
                (retok (cpp-stmt-return-void) tok-span parstate))
               (parstate (if peek? (unread-token parstate) parstate))
               ((erp e & parstate) (parse-cpp-expr parstate))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after return expression"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-return-expr :e e) span parstate)))
         ;; 'break' statement
         ((when (token-keywordp tok? "break"))
          (b* (((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after 'break'"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (cpp-stmt-break) span parstate)))
         ;; 'continue' statement
         ((when (token-keywordp tok? "continue"))
          (b* (((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after 'continue'"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (cpp-stmt-continue) span parstate)))
         ;; 'goto' label;
         ((when (token-keywordp tok? "goto"))
          (b* (((erp lbl? lbl-span parstate) (read-token parstate))
               ((unless (and lbl? (token-case lbl? :ident)))
                (reterr-msg :where (span->start lbl-span)
                            :expected "label identifier after 'goto'"
                            :found lbl?
                            :extra nil))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after goto"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-goto :label (token-ident->ident lbl?))
                   span parstate)))
         ;; 'if' ['constexpr'] '(' expr ')' stmt [ 'else' stmt ]
         ((when (token-keywordp tok? "if"))
          (b* (;; Optional 'constexpr' keyword (C++17 if constexpr)
               ((erp cx? & parstate) (read-token parstate))
               (constexprp (token-cpp-kw-p cx? "constexpr"))
               ;; Put back the token if it wasn't 'constexpr'
               (parstate (if (and cx? (not constexprp))
                             (unread-token parstate)
                           parstate))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'if'"
                            :found lp?
                            :extra nil))
               ((erp test & parstate) (parse-cpp-expr parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after if-test"
                            :found rp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp then then-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               ((erp e? & parstate) (read-token parstate))
               ((when (token-keywordp e? "else"))
                (b* (((erp else else-span parstate)
                      (parse-cpp-stmt parstate))
                     ((unless (<= (parsize parstate) psize))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end else-span))))
                  (retok (make-cpp-stmt-if-else
                          :constexprp constexprp
                          :test test :then then :else else)
                         span parstate)))
               (parstate (if e? (unread-token parstate) parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end then-span))))
            (retok (make-cpp-stmt-if-then
                    :constexprp constexprp
                    :test test :then then)
                   span parstate)))
         ;; 'while' '(' expr ')' stmt
         ((when (token-keywordp tok? "while"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'while'"
                            :found lp?
                            :extra nil))
               ((erp test & parstate) (parse-cpp-expr parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after while-test"
                            :found rp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end body-span))))
            (retok (make-cpp-stmt-while :test test :body body)
                   span parstate)))
         ;; 'do' stmt 'while' '(' expr ')' ';'
         ((when (token-keywordp tok? "do"))
          (b* (((erp body & parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               ((erp wh? wh-span parstate) (read-token parstate))
               ((unless (token-keywordp wh? "while"))
                (reterr-msg :where (span->start wh-span)
                            :expected "'while' after 'do' body"
                            :found wh?
                            :extra nil))
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'do ... while'"
                            :found lp?
                            :extra nil))
               ((erp test & parstate) (parse-cpp-expr parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after do-while test"
                            :found rp?
                            :extra nil))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after do-while"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-dowhile :body body :test test)
                   span parstate)))
         ;; 'throw' ';' or 'throw' expr ';'  (as a statement)
         ((when (token-cpp-kw-p tok? "throw"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ((when (token-punctuatorp peek? ";"))
                (retok (cpp-stmt-rethrow) tok-span parstate))
               (parstate (if peek? (unread-token parstate) parstate))
               ((erp e & parstate) (parse-cpp-expr parstate))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after throw"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-throw-stmt :e e) span parstate)))
         ;; 'switch' '(' expr ')' stmt
         ((when (token-keywordp tok? "switch"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'switch'"
                            :found lp?
                            :extra nil))
               ((erp test & parstate) (parse-cpp-expr parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after switch test"
                            :found rp?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end body-span))))
            (retok (make-cpp-stmt-switch :target test :body body)
                   span parstate)))
         ;; 'case' expr ':' stmt
         ((when (token-keywordp tok? "case"))
          (b* (((erp e & parstate) (parse-cpp-assign-or-cond parstate))
               ((erp colon? colon-span parstate) (read-token parstate))
               ((unless (token-punctuatorp colon? ":"))
                (reterr-msg :where (span->start colon-span)
                            :expected "':' after case label"
                            :found colon?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp s s-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end s-span))))
            (retok (make-cpp-stmt-caselbl :e e :s s) span parstate)))
         ;; 'default' ':' stmt
         ((when (token-keywordp tok? "default"))
          (b* (((erp colon? colon-span parstate) (read-token parstate))
               ((unless (token-punctuatorp colon? ":"))
                (reterr-msg :where (span->start colon-span)
                            :expected "':' after 'default'"
                            :found colon?
                            :extra nil))
               ((erp s s-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end s-span))))
            (retok (make-cpp-stmt-default :s s) span parstate)))
         ;; 'try' '{' body '}' catch-clause-list
         ((when (token-cpp-kw-p tok? "try"))
          (b* (((erp lb? lb-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lb? "{"))
                (reterr-msg :where (span->start lb-span)
                            :expected "'{' after 'try'"
                            :found lb?
                            :extra nil))
               (psize2 (parsize parstate))
               ((erp body & parstate)
                (parse-cpp-block-item-list-body parstate))
               ((unless (<= (parsize parstate) psize2))
                (reterr :impossible))
               ((erp rb? rb-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rb? "}"))
                (reterr-msg :where (span->start rb-span)
                            :expected "'}' to close try body"
                            :found rb?
                            :extra nil))
               ;; parsize < psize because we've consumed '{' and '}' at minimum
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp handlers close-span parstate)
                (parse-cpp-catch-clause-list parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end close-span))))
            (retok (make-cpp-stmt-try :body body :handlers handlers)
                   span parstate)))
         ;; 'for' '(' <init> ; <test> ; <next> ')' stmt
         ;;      or 'for' '(' type name : range ')' stmt
         ((when (token-keywordp tok? "for"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'for'"
                            :found lp?
                            :extra nil))
               ;; Peek first token after '(' to discriminate init form
               ((erp f1? & parstate) (read-token parstate))
               ;; Empty init: 'for' '(' ';' [test] ; [next] ) body
               ((when (token-punctuatorp f1? ";"))
                (b* (((erp test-p test-e parstate)
                      (parse-cpp-for-opt-test parstate))
                     ((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp next-p next-e parstate)
                      (parse-cpp-for-opt-next parstate))
                     ((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp body body-span parstate) (parse-cpp-stmt parstate))
                     ((unless (<= (parsize parstate) psize))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end body-span))))
                  (retok (make-cpp-stmt-for-expr
                          :init-e-p nil
                          :init-e (irr-cpp-expr)
                          :test-e-p test-p
                          :test-e test-e
                          :next-e-p next-p
                          :next-e next-e
                          :body body)
                         span parstate)))
               ;; Decide: declaration or expression init?
               ((mv declp parstate)
                (if (or (and f1? (token-case f1? :keyword))
                        (token-keywordp f1? "const")
                        (token-keywordp f1? "volatile"))
                    ;; Type keyword first: declaration
                    (b* ((parstate
                          (if f1? (unread-token parstate) parstate)))
                      (mv t parstate))
                  (if (and f1? (token-case f1? :ident))
                      ;; Ident first: peek second token
                      (b* (((mv erp2 f2? & parstate) (read-token parstate))
                           (two-ident-p
                            (and (not erp2)
                                 f2?
                                 (token-case f2? :ident)))
                           ;; Put f2? back
                           (parstate
                            (if (and (not erp2) f2?)
                                (unread-token parstate)
                              parstate))
                           ;; Put f1? back
                           (parstate
                            (if f1? (unread-token parstate) parstate)))
                        (mv two-ident-p parstate))
                    ;; Not a keyword or ident: expression form
                    (b* ((parstate
                          (if f1? (unread-token parstate) parstate)))
                      (mv nil parstate)))))
               ((when declp)
                ;; for ( type name [: range | [= init] ; test ; next ] ) body
                (b* (((erp type & parstate) (parse-cpp-type-spec-full parstate))
                     ((erp name? name-span parstate) (read-token parstate))
                     ((unless (and name? (token-case name? :ident)))
                      (reterr-msg :where (span->start name-span)
                                  :expected "name in for-loop declaration"
                                  :found name?
                                  :extra nil))
                     (name-ident (token-ident->ident name?))
                     ((erp sep? & parstate) (read-token parstate))
                     ;; ':' → range-based for
                     ((when (token-punctuatorp sep? ":"))
                      (b* (((unless (< (parsize parstate) psize))
                            (reterr :impossible))
                           ((erp range & parstate) (parse-cpp-expr parstate))
                           ((erp rp? rp-span parstate) (read-token parstate))
                           ((unless (token-punctuatorp rp? ")"))
                            (reterr-msg
                             :where (span->start rp-span)
                             :expected "')' after for-range initializer"
                             :found rp?
                             :extra nil))
                           ((unless (< (parsize parstate) psize))
                            (reterr :impossible))
                           ((erp body body-span parstate)
                            (parse-cpp-stmt parstate))
                           ((unless (<= (parsize parstate) psize))
                            (reterr :impossible))
                           (span (make-span :start (span->start tok-span)
                                            :end   (span->end body-span))))
                        (retok (make-cpp-stmt-for-range
                                :type type
                                :name name-ident
                                :range range
                                :body body)
                               span parstate)))
                     ;; '=' or ';' → traditional for-decl
                     ((mv init-p init parstate)
                      (cond
                       ((token-punctuatorp sep? "=")
                        (b* (((unless (< (parsize parstate) psize))
                              (mv nil (irr-cpp-expr) parstate))
                             ((mv erp3 ie & parstate)
                              (parse-cpp-assign-or-cond parstate)))
                          (if erp3
                              (mv nil (irr-cpp-expr) parstate)
                            (mv t ie parstate))))
                       ((token-punctuatorp sep? ";")
                        ;; ';' was the separator — put it back as semi1
                        (b* ((parstate (unread-token parstate)))
                          (mv nil (irr-cpp-expr) parstate)))
                       (t
                        (b* ((parstate
                              (if sep? (unread-token parstate) parstate)))
                          (mv nil (irr-cpp-expr) parstate)))))
                     ((erp semi1? semi1-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi1? ";"))
                      (reterr-msg :where (span->start semi1-span)
                                  :expected "';' in for-decl"
                                  :found semi1?
                                  :extra nil))
                     ((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp test-p test-e parstate)
                      (parse-cpp-for-opt-test parstate))
                     ((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp next-p next-e parstate)
                      (parse-cpp-for-opt-next parstate))
                     ((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp body body-span parstate) (parse-cpp-stmt parstate))
                     ((unless (<= (parsize parstate) psize))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end body-span))))
                  (retok (make-cpp-stmt-for-decl
                          :type type
                          :name name-ident
                          :init-p init-p
                          :init init
                          :test-p test-p
                          :test test-e
                          :next-p next-p
                          :next next-e
                          :body body)
                         span parstate)))
               ;; Expression init: f1? is first token of init expression
               (parstate (if f1? (unread-token parstate) parstate))
               ((erp init-e & parstate) (parse-cpp-expr parstate))
               ((erp semi1? semi1-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi1? ";"))
                (reterr-msg :where (span->start semi1-span)
                            :expected "';' after for-expr init"
                            :found semi1?
                            :extra nil))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp test-p test-e parstate)
                (parse-cpp-for-opt-test parstate))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp next-p next-e parstate)
                (parse-cpp-for-opt-next parstate))
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end body-span))))
            (retok (make-cpp-stmt-for-expr
                    :init-e-p t
                    :init-e init-e
                    :test-e-p test-p
                    :test-e test-e
                    :next-e-p next-p
                    :next-e next-e
                    :body body)
                   span parstate)))
         ;; 'co_yield' expr ';'
         ((when (token-cpp-kw-p tok? "co_yield"))
          (b* (((erp e & parstate) (parse-cpp-expr parstate))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after co_yield expression"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-co-yield :e e) span parstate)))
         ;; 'co_return' [expr] ';'
         ((when (token-cpp-kw-p tok? "co_return"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ((when (token-punctuatorp peek? ";"))
                (retok (cpp-stmt-co-return-void) tok-span parstate))
               (parstate (if peek? (unread-token parstate) parstate))
               ((erp e & parstate) (parse-cpp-expr parstate))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after co_return expression"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-stmt-co-return-expr :e e) span parstate)))
         ;; Labeled statement: ident ':' stmt
         ;; Must be checked before expression-statement fallthrough.
         ((mv labelp label-ident label-tok-span parstate)
          (if (and tok? (token-case tok? :ident))
              (b* (((mv erp2 tok2? tok2-span parstate) (read-token parstate)))
                (if (and (not erp2) (token-punctuatorp tok2? ":"))
                    ;; ident ':' — labeled statement; tok2? consumed (the ':')
                    (mv t (token-ident->ident tok?) tok-span parstate)
                  ;; Not a label — put tok2? back
                  (b* ((parstate
                        (if (and (not erp2) tok2?)
                            (unread-token parstate)
                          parstate)))
                    (mv nil (c$::irr-ident)
                        (c$::span-fix tok2-span) parstate))))
            (mv nil (c$::irr-ident) (c$::span-fix tok-span) parstate)))
         ((when labelp)
          (b* (((erp s s-span parstate) (parse-cpp-stmt parstate))
               ((unless (<= (parsize parstate) psize))
                (reterr :impossible))
               (span (make-span :start (span->start label-tok-span)
                                :end   (span->end s-span))))
            (retok (make-cpp-stmt-labeled :label label-ident :s s)
                   span parstate)))
         ;; Fallthrough: expression statement.  Put back the token and parse
         ;; a full expression, then expect ';'.
         (parstate (if tok? (unread-token parstate) parstate))
         ((erp e & parstate) (parse-cpp-expr parstate))
         ((erp semi? semi-span parstate) (read-token parstate))
         ((unless (token-punctuatorp semi? ";"))
          (reterr-msg :where (span->start semi-span)
                      :expected "';' after expression statement"
                      :found semi?
                      :extra nil))
         (span (make-span :start (span->start tok-span)
                          :end   (span->end semi-span))))
      (retok (make-cpp-stmt-expr-stmt :e e) span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse one block item: either a local declaration or a statement.
  ;;
  ;; Discrimination heuristic: a block item is treated as a declaration
  ;; if its first two tokens are both identifiers (e.g., "MyType x") OR
  ;; the first token is "const" or "volatile".  Otherwise it is a statement.
  ;;
  ;; This is conservative: built-in types like "int" arrive as C keywords
  ;; (token-keyword, not token-ident), so "int x" would also be classified
  ;; as a declaration via the keyword check.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-block-item ((parstate parstatep))
    :returns (mv erp
                 (item cpp-block-item-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 7)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-block-item) (irr-span) parstate)
         ((erp t1? t1-span parstate) (read-token parstate))
         ;; Detect "type" prefix: const, volatile, or a C built-in
         ;; type keyword.
         (declp-kw (or (token-keywordp t1? "const")
                       (token-keywordp t1? "volatile")
                       (token-keywordp t1? "int")
                       (token-keywordp t1? "char")
                       (token-keywordp t1? "short")
                       (token-keywordp t1? "long")
                       (token-keywordp t1? "float")
                       (token-keywordp t1? "double")
                       (token-keywordp t1? "void")
                       (token-keywordp t1? "signed")
                       (token-keywordp t1? "unsigned")
                       (token-cpp-kw-p t1? "bool")
                       (token-keywordp t1? "auto")))
         ;; If first token is an ident, check if the next token is also an
         ;; ident (e.g., "MyType x").  In that case treat as decl.
         ((mv declp-ident parstate)
          (if (and t1? (token-case t1? :ident) (not declp-kw))
              (b* (((mv erp2 t2? & parstate) (read-token parstate))
                   (parstate (if (and (not erp2) t2?)
                                 (unread-token parstate)
                               parstate)))
                (mv (and (not erp2)
                         t2?
                         (token-case t2? :ident))
                    parstate))
            (mv nil parstate)))
         (declp (or declp-kw declp-ident))
         ;; Restore t1?
         (parstate (if t1? (unread-token parstate) parstate))
         ((when declp)
          ;; Parse a local declaration: type-spec ident [= init] ';'
          (b* ((psize (parsize parstate))
               ((erp type & parstate) (parse-cpp-type-spec-full parstate))
               ((erp name? name-span parstate) (read-token parstate))
               ((unless (and name? (token-case name? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "name in local declaration"
                            :found name?
                            :extra nil))
               ((erp peek? & parstate) (read-token parstate))
               ((mv init-p init parstate)
                (cond ((token-punctuatorp peek? "=")
                       (b* (((unless (< (parsize parstate) psize))
                             (mv nil (irr-cpp-expr) parstate))
                            ((mv erp2 e & parstate)
                             (parse-cpp-assign-or-cond parstate))
                            ((when erp2)
                             (mv nil (irr-cpp-expr) parstate)))
                         (mv t e parstate)))
                      (peek? (b* ((parstate (unread-token parstate)))
                               (mv nil (irr-cpp-expr) parstate)))
                      (t (mv nil (irr-cpp-expr) parstate))))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after declaration"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start t1-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-block-item-decl
                    :type type
                    :name (token-ident->ident name?)
                    :init-p init-p
                    :init init)
                   span parstate)))
         ;; Otherwise: a statement
         ((erp s s-span parstate) (parse-cpp-stmt parstate)))
      (retok (make-cpp-block-item-stmt :stmt s) s-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse a sequence of block items until '}' or EOF.  Does NOT consume '}'.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-block-item-list-body ((parstate parstatep))
    :returns (mv erp
                 (items cpp-block-item-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 8)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         ((erp peek? peek-span parstate) (read-token parstate))
         ((when (or (not peek?)
                    (token-punctuatorp peek? "}")))
          (b* ((parstate (if peek? (unread-token parstate) parstate)))
            (retok nil peek-span parstate)))
         (parstate (unread-token parstate))
         (psize (parsize parstate))
         ((erp item item-span parstate) (parse-cpp-block-item parstate))
         ((unless (< (parsize parstate) psize))
          (reterr :impossible))
         ((erp rest & parstate) (parse-cpp-block-item-list-body parstate)))
      (retok (cons item rest) item-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse one C++ catch clause: 'catch' '(' handler ')' '{' body '}'.
  ;; Rank 3 in the mutual block (calls block-item-list-body at rank 2).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-catch-clause ((parstate parstatep))
    :returns (mv erp
                 (clause cpp-catch-clause-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 7)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-catch-clause) (irr-span) parstate)
         ((erp handler header-span parstate)
          (parse-cpp-exception-handler-header parstate))
         ((erp open? open-span parstate) (read-token parstate))
         ((unless (token-punctuatorp open? "{"))
          (reterr-msg :where (span->start open-span)
                      :expected "'{' to begin catch body"
                      :found open?
                      :extra nil))
         ((erp body & parstate) (parse-cpp-block-item-list-body parstate))
         ((erp close? close-span parstate) (read-token parstate))
         ((unless (token-punctuatorp close? "}"))
          (reterr-msg :where (span->start close-span)
                      :expected "'}' to close catch body"
                      :found close?
                      :extra nil))
         (span (make-span :start (span->start header-span)
                          :end   (span->end close-span))))
      (retok (make-cpp-catch-clause :handler handler :body body) span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse zero or more C++ catch clauses.
  ;; Rank 4 in the mutual block (calls catch-clause at rank 3).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-catch-clause-list ((parstate parstatep))
    :returns (mv erp
                 (clauses cpp-catch-clause-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 8)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         (psize-list (parsize parstate))
         ((erp peek? peek-span parstate) (read-token parstate))
         ((unless (token-cpp-kw-p peek? "catch"))
          (b* ((parstate (if peek? (unread-token parstate) parstate)))
            (retok nil peek-span parstate)))
         (parstate (unread-token parstate))
         ((erp clause & parstate) (parse-cpp-catch-clause parstate))
         ;; catch-clause cond guarantees parsize < psize-list on success
         ((unless (< (parsize parstate) psize-list))
          (reterr :impossible))
         ((erp rest & parstate) (parse-cpp-catch-clause-list parstate)))
      (retok (cons clause rest) peek-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Type specifier parser with full decltype(expr) support.
  ;; This variant is mutually recursive because the :decltype case calls
  ;; parse-cpp-assign-or-cond to parse an arbitrary expression.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-type-spec-full ((parstate parstatep))
    :returns (mv erp
                 (spec cpp-type-spec-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse a C++ type specifier, supporting complex @('decltype(expr)')."
    :long
    (xdoc::topstring
     (xdoc::p
      "This variant of the type-specifier parser is defined inside the
       mutually-recursive expression/statement block so that it can call
       @(tsee parse-cpp-assign-or-cond) for the argument of @('decltype').
       For all forms other than @('decltype(expr)'), it delegates to the
       simpler @(tsee parse-cpp-type-spec)."))
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (declare (xargs :ruler-extenders :all))
    (b* (((reterr) (irr-cpp-type-spec) (irr-span) parstate)
         ;; Capture the original parsize before any reads, for the MBT guard
         ;; that justifies the upward-rank call to parse-cpp-assign-or-cond.
         (psize (parsize parstate))
         ;; Peek at the first token to detect 'decltype'
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; If the first token is the identifier 'decltype', handle the
         ;; complex-expression case.
         ((when (and tok?
                     (token-case tok? :ident)
                     (equal (ident->unwrap (token-ident->ident tok?)) "decltype")))
          (b* (;; Read '('
               ((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'decltype'"
                            :found lp?
                            :extra nil))
               ;; We have consumed 'decltype' and '(' — parsize is now strictly
               ;; less than psize (the original). Assert this before calling the
               ;; higher-rank parse-cpp-assign-or-cond (rank 4 vs our rank 0).
               ((unless (< (parsize parstate) psize))
                (reterr :impossible))
               ;; Parse the full expression (e.g., a+b, fn(), *p)
               ((erp inner & parstate) (parse-cpp-assign-or-cond parstate))
               ;; Read ')'
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after 'decltype' expression"
                            :found rp?
                            :extra nil))
               (base-span (make-span :start (span->start tok-span)
                                     :end   (span->end rp-span)))
               (base (make-cpp-type-spec-decltype :arg inner))
               ;; Apply optional pointer/reference suffix
               ((erp result result-span parstate)
                (parse-cpp-type-spec-suffix base base-span parstate)))
            (retok result result-span parstate)))
         ;; Not 'decltype' — put back token and use the simple parser
         (parstate (if tok? (unread-token parstate) parstate))
         ((erp spec spec-span parstate) (parse-cpp-type-spec parstate)))
      (retok spec spec-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Full capture-item parser: like parse-cpp-one-capture but supports
  ;; C++14 init-captures [x = expr] and [&x = expr] by calling
  ;; parse-cpp-assign-or-cond (rank 4 upward, justified by 2+ tokens consumed).
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-one-capture-full ((parstate parstatep))
    :returns (mv erp
                 (cap cpp-capture-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse one C++ lambda capture, including C++14 init-captures."
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (declare (xargs :ruler-extenders :all))
    (b* (((reterr) (irr-cpp-capture) (irr-span) parstate)
         ;; Capture parsize before any reads, for upward-rank MBT guards.
         (psize (parsize parstate))
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; '=' -> default by-value [=]
         ((when (token-punctuatorp tok? "="))
          (retok (cpp-capture-default-val) tok-span parstate))
         ;; '&' -> peek: by-ref named, init-ref-capture, or default-ref
         ((when (token-punctuatorp tok? "&"))
          (b* (((erp next? next-span parstate) (read-token parstate))
               ((when (and next? (token-case next? :ident)))
                (b* (;; Peek for '=' to detect init-capture [&x = expr]
                     ((erp eq? & parstate) (read-token parstate))
                     ((when (token-punctuatorp eq? "="))
                      ;; Init-ref-capture: consumed '&', ident, '=' — 3 tokens
                      (b* (((unless (< (parsize parstate) psize))
                            (reterr :impossible))
                           ((erp init & parstate)
                            (parse-cpp-assign-or-cond parstate))
                           (span (make-span :start (span->start tok-span)
                                            :end   (span->end next-span))))
                        (retok (make-cpp-capture-ref-init
                                :name (token-ident->ident next?)
                                :expr init)
                               span parstate)))
                     ;; Not '=' — plain by-ref named capture [&x]
                     (parstate (if eq? (unread-token parstate) parstate)))
                  (retok (make-cpp-capture-by-ref
                          :name (token-ident->ident next?))
                         (make-span :start (span->start tok-span)
                                    :end   (span->end next-span))
                         parstate)))
               ;; Not an ident — default-ref [&]
               (parstate (if next? (unread-token parstate) parstate)))
            (retok (cpp-capture-default-ref) tok-span parstate)))
         ;; 'this' -> capture this [this]
         ;; 'this' is a C++-only keyword; in C17 mode it arrives as token-ident.
         ((when (token-cpp-kw-p tok? "this"))
          (retok (cpp-capture-this) tok-span parstate))
         ;; '*' followed by 'this' -> capture [*this] (C++17)
         ((when (token-punctuatorp tok? "*"))
          (b* (((erp this? this-span parstate) (read-token parstate))
               ((unless (token-cpp-kw-p this? "this"))
                (reterr-msg :where (span->start this-span)
                            :expected "'this' after '*' in capture list"
                            :found this?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end this-span))))
            (retok (cpp-capture-star-this) span parstate)))
         ;; identifier -> by-value capture [x], or init-capture [x = expr]
         ((when (and tok? (token-case tok? :ident)))
          (b* (;; Peek for '=' to detect init-capture [x = expr]
               ((erp eq? & parstate) (read-token parstate))
               ((when (token-punctuatorp eq? "="))
                ;; Init-capture by value: consumed ident and '=' — 2 tokens
                (b* (((unless (< (parsize parstate) psize))
                      (reterr :impossible))
                     ((erp init & parstate)
                      (parse-cpp-assign-or-cond parstate)))
                  (retok (make-cpp-capture-init
                          :name (token-ident->ident tok?)
                          :expr init)
                         tok-span parstate)))
               ;; Not '=' — plain by-value capture [x]
               (parstate (if eq? (unread-token parstate) parstate)))
            (retok (make-cpp-capture-by-value
                    :name (token-ident->ident tok?))
                   tok-span parstate))))
      ;; Anything else is an error
      (reterr-msg :where (span->start tok-span)
                  :expected "capture item ('=', '&', 'this', '*this', or identifier)"
                  :found tok?
                  :extra nil)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Full captures-rest: like parse-cpp-captures-rest but calls
  ;; parse-cpp-one-capture-full so init-captures are supported.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-captures-rest-full ((acc cpp-capture-listp)
                                        (parstate parstatep))
    :returns (mv erp
                 (captures cpp-capture-listp)
                 (close-span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse remaining captures after the first, consuming the closing ']'."
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (declare (xargs :ruler-extenders :all))
    (b* (((reterr) nil (irr-span) parstate)
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; ']' closes the capture list; return the accumulated captures
         ((when (token-punctuatorp tok? "]"))
          (retok (cpp-capture-list-fix acc) tok-span parstate))
         ;; Must be ','
         ((unless (token-punctuatorp tok? ","))
          (reterr-msg :where (span->start tok-span)
                      :expected "',' or ']' in capture list"
                      :found tok?
                      :extra nil))
         ;; psize AFTER consuming ',' — strictly less than original parsize
         (psize (parsize parstate))
         ;; Parse next capture (same rank 0, parsize already < original)
         ((erp cap & parstate) (parse-cpp-one-capture-full parstate))
         ;; MBT bound: parsize did not grow
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Self-recursive call: parsize <= psize < original parsize ✓
         ((erp rest close-span parstate)
          (parse-cpp-captures-rest-full
           (append (cpp-capture-list-fix acc) (list cap)) parstate)))
      (retok rest close-span parstate)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Full capture-list: like parse-cpp-capture-list but supports init-captures.
  ;; Called with open-span = span of already-consumed '[', parstate = after '['.
  ;; Inlines the first-capture logic so no peek-unread is needed; all calls to
  ;; parse-cpp-captures-rest-full are guarded by MBT to establish termination.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-capture-list-full ((open-span spanp)
                                       (parstate parstatep))
    :returns (mv erp
                 (captures cpp-capture-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse a C++ lambda capture list after @('[') has been consumed."
    :long "<p>@('open-span') is the span of the already-consumed @('[').
           @('parstate') is the parser state after consuming @('[').</p>"
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         ;; Capture parsize before any reads; all paths below consume >= 1 token
         ;; before calling parse-cpp-captures-rest-full (or assign-or-cond).
         (psize (parsize parstate))
         ;; Read the first token to dispatch.
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; Empty capture list '[]'.
         ((when (token-punctuatorp tok? "]"))
          (retok nil
                 (make-span :start (span->start open-span)
                             :end   (span->end tok-span))
                 parstate))
         ;; '=' -> default by-value capture [=].
         ((when (token-punctuatorp tok? "="))
          (b* (((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
               ((erp rest close-span parstate)
                (parse-cpp-captures-rest-full (list (cpp-capture-default-val)) parstate)))
            (retok rest
                   (make-span :start (span->start open-span) :end (span->end close-span))
                   parstate)))
         ;; '&' -> default-ref [&], named by-ref [&x], or init-ref-capture [&x = expr].
         ((when (token-punctuatorp tok? "&"))
          (b* (((erp next? & parstate) (read-token parstate))
               ;; ident after '&': named by-ref or init-ref-capture.
               ((when (and next? (token-case next? :ident)))
                (b* (((erp eq? & parstate) (read-token parstate))
                     ((when (token-punctuatorp eq? "="))
                      ;; Init-ref-capture [&x = expr]: consumed '&', ident, '='.
                      (b* (((unless (< (parsize parstate) psize)) (reterr :impossible))
                           ((erp init & parstate) (parse-cpp-assign-or-cond parstate))
                           ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
                           (first (make-cpp-capture-ref-init
                                   :name (token-ident->ident next?)
                                   :expr init))
                           ((erp rest close-span parstate)
                            (parse-cpp-captures-rest-full (list first) parstate)))
                        (retok rest
                               (make-span :start (span->start open-span) :end (span->end close-span))
                               parstate)))
                     ;; Not '=' — plain by-ref named [&x].
                     (parstate (if eq? (unread-token parstate) parstate))
                     (first (make-cpp-capture-by-ref :name (token-ident->ident next?)))
                     ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
                     ((erp rest close-span parstate)
                      (parse-cpp-captures-rest-full (list first) parstate)))
                  (retok rest
                         (make-span :start (span->start open-span) :end (span->end close-span))
                         parstate)))
               ;; Not an ident after '&' — default-ref [&].
               (parstate (if next? (unread-token parstate) parstate))
               ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
               ((erp rest close-span parstate)
                (parse-cpp-captures-rest-full (list (cpp-capture-default-ref)) parstate)))
            (retok rest
                   (make-span :start (span->start open-span) :end (span->end close-span))
                   parstate)))
         ;; 'this' -> [this].
         ((when (token-cpp-kw-p tok? "this"))
          (b* (((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
               ((erp rest close-span parstate)
                (parse-cpp-captures-rest-full (list (cpp-capture-this)) parstate)))
            (retok rest
                   (make-span :start (span->start open-span) :end (span->end close-span))
                   parstate)))
         ;; '*' followed by 'this' -> [*this].
         ((when (token-punctuatorp tok? "*"))
          (b* (((erp this? this-span parstate) (read-token parstate))
               ((unless (token-cpp-kw-p this? "this"))
                (reterr-msg :where (span->start this-span)
                            :expected "'this' after '*' in capture list"
                            :found this?
                            :extra nil))
               ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
               ((erp rest close-span parstate)
                (parse-cpp-captures-rest-full (list (cpp-capture-star-this)) parstate)))
            (retok rest
                   (make-span :start (span->start open-span) :end (span->end close-span))
                   parstate)))
         ;; ident -> by-value [x] or init-capture [x = expr].
         ((when (and tok? (token-case tok? :ident)))
          (b* (((erp eq? & parstate) (read-token parstate))
               ((when (token-punctuatorp eq? "="))
                ;; Init-capture [x = expr]: consumed ident and '='.
                (b* (((unless (< (parsize parstate) psize)) (reterr :impossible))
                     ((erp init & parstate) (parse-cpp-assign-or-cond parstate))
                     ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
                     (first (make-cpp-capture-init
                             :name (token-ident->ident tok?)
                             :expr init))
                     ((erp rest close-span parstate)
                      (parse-cpp-captures-rest-full (list first) parstate)))
                  (retok rest
                         (make-span :start (span->start open-span) :end (span->end close-span))
                         parstate)))
               ;; Not '=' — plain by-value [x].
               (parstate (if eq? (unread-token parstate) parstate))
               (first (make-cpp-capture-by-value :name (token-ident->ident tok?)))
               ((unless (mbt (< (parsize parstate) psize))) (reterr :impossible))
               ((erp rest close-span parstate)
                (parse-cpp-captures-rest-full (list first) parstate)))
            (retok rest
                   (make-span :start (span->start open-span) :end (span->end close-span))
                   parstate))))
      ;; Unexpected token as first capture item.
      (reterr-msg :where (span->start tok-span)
                  :expected "capture item ('=', '&', 'this', '*this', ']', or identifier)"
                  :found tok?
                  :extra nil)))

  ///

  (defthm-parse-cpp-full-mutual-flag
    parsize-of-parse-cpp-full-mutual-uncond
    (defthm parsize-of-parse-cpp-primary-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-primary parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-primary)
    (defthm parsize-of-parse-cpp-arg-list-rest-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-arg-list-rest acc parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-arg-list-rest)
    (defthm parsize-of-parse-cpp-postfix-rest-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-postfix-rest lhs lhs-span parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-postfix-rest)
    (defthm parsize-of-parse-cpp-unary-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-unary parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-unary)
    (defthm parsize-of-parse-cpp-pratt-loop-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-pratt-loop
                              min-prec lhs lhs-span parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-pratt-loop)
    (defthm parsize-of-parse-cpp-cond-rest-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-cond-rest test test-span parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-cond-rest)
    (defthm parsize-of-parse-cpp-assign-or-cond-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-assign-or-cond parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-assign-or-cond)
    (defthm parsize-of-parse-cpp-expr-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-expr parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-expr)
    (defthm parsize-of-parse-cpp-for-opt-test-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-for-opt-test parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-for-opt-test)
    (defthm parsize-of-parse-cpp-for-opt-next-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-for-opt-next parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-for-opt-next)
    (defthm parsize-of-parse-cpp-stmt-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-stmt parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-stmt)
    (defthm parsize-of-parse-cpp-block-item-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-block-item parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-block-item)
    (defthm parsize-of-parse-cpp-block-item-list-body-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-block-item-list-body parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-block-item-list-body)
    (defthm parsize-of-parse-cpp-catch-clause-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-catch-clause parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-catch-clause)
    (defthm parsize-of-parse-cpp-catch-clause-list-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-catch-clause-list parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-catch-clause-list)
    (defthm parsize-of-parse-cpp-type-spec-full-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-type-spec-full parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-type-spec-full)
    (defthm parsize-of-parse-cpp-one-capture-full-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-one-capture-full parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-one-capture-full)
    (defthm parsize-of-parse-cpp-captures-rest-full-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-captures-rest-full acc parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-captures-rest-full)
    (defthm parsize-of-parse-cpp-capture-list-full-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-capture-list-full open-span parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-capture-list-full)
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-read-token-uncond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-suffix-uncond
                                parsize-of-parse-cpp-exception-handler-header-uncond
                                parsize-of-parse-cpp-param-list-uncond
                                parsize-of-parse-cpp-capture-list-uncond)
             :expand ((parse-cpp-primary parstate)
                      (parse-cpp-arg-list-rest acc parstate)
                      (parse-cpp-postfix-rest lhs lhs-span parstate)
                      (parse-cpp-unary parstate)
                      (parse-cpp-pratt-loop min-prec lhs lhs-span parstate)
                      (parse-cpp-cond-rest test test-span parstate)
                      (parse-cpp-assign-or-cond parstate)
                      (parse-cpp-expr parstate)
                      (parse-cpp-for-opt-test parstate)
                      (parse-cpp-for-opt-next parstate)
                      (parse-cpp-stmt parstate)
                      (parse-cpp-block-item parstate)
                      (parse-cpp-block-item-list-body parstate)
                      (parse-cpp-catch-clause parstate)
                      (parse-cpp-catch-clause-list parstate)
                      (parse-cpp-type-spec-full parstate)
                      (parse-cpp-one-capture-full parstate)
                      (parse-cpp-captures-rest-full acc parstate)
                      (parse-cpp-capture-list-full open-span parstate)))))

  (defthm-parse-cpp-full-mutual-flag
    parsize-of-parse-cpp-full-mutual-cond
    (defthm parsize-of-parse-cpp-primary-cond
      (implies (not (mv-nth 0 (parse-cpp-primary parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-primary parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-primary)
    (defthm parsize-of-parse-cpp-arg-list-rest-cond
      (implies (not (mv-nth 0 (parse-cpp-arg-list-rest acc parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-arg-list-rest acc parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-arg-list-rest)
    (defthm parsize-of-parse-cpp-postfix-rest-cond
      t
      :rule-classes nil
      :flag parse-cpp-postfix-rest)
    (defthm parsize-of-parse-cpp-unary-cond
      (implies (not (mv-nth 0 (parse-cpp-unary parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-unary parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-unary)
    (defthm parsize-of-parse-cpp-pratt-loop-cond
      t
      :rule-classes nil
      :flag parse-cpp-pratt-loop)
    (defthm parsize-of-parse-cpp-cond-rest-cond
      (implies (not (mv-nth 0 (parse-cpp-cond-rest test test-span parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-cond-rest test test-span parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-cond-rest)
    (defthm parsize-of-parse-cpp-assign-or-cond-cond
      (implies (not (mv-nth 0 (parse-cpp-assign-or-cond parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-assign-or-cond parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-assign-or-cond)
    (defthm parsize-of-parse-cpp-expr-cond
      (implies (not (mv-nth 0 (parse-cpp-expr parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-expr parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-expr)
    (defthm parsize-of-parse-cpp-for-opt-test-cond
      (implies (not (mv-nth 0 (parse-cpp-for-opt-test parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-for-opt-test parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-for-opt-test)
    (defthm parsize-of-parse-cpp-for-opt-next-cond
      (implies (not (mv-nth 0 (parse-cpp-for-opt-next parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-for-opt-next parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-for-opt-next)
    (defthm parsize-of-parse-cpp-stmt-cond
      (implies (not (mv-nth 0 (parse-cpp-stmt parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-stmt parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-stmt)
    (defthm parsize-of-parse-cpp-block-item-cond
      (implies (not (mv-nth 0 (parse-cpp-block-item parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-block-item parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-block-item)
    (defthm parsize-of-parse-cpp-block-item-list-body-cond
      t
      :rule-classes nil
      :flag parse-cpp-block-item-list-body)
    (defthm parsize-of-parse-cpp-catch-clause-cond
      (implies (not (mv-nth 0 (parse-cpp-catch-clause parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-catch-clause parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-catch-clause)
    (defthm parsize-of-parse-cpp-catch-clause-list-cond
      t
      :rule-classes nil
      :flag parse-cpp-catch-clause-list)
    (defthm parsize-of-parse-cpp-type-spec-full-cond
      (implies (not (mv-nth 0 (parse-cpp-type-spec-full parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-type-spec-full parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-type-spec-full)
    (defthm parsize-of-parse-cpp-one-capture-full-cond
      (implies (not (mv-nth 0 (parse-cpp-one-capture-full parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-one-capture-full parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-one-capture-full)
    (defthm parsize-of-parse-cpp-captures-rest-full-cond
      (implies (not (mv-nth 0 (parse-cpp-captures-rest-full acc parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-captures-rest-full acc parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-captures-rest-full)
    (defthm parsize-of-parse-cpp-capture-list-full-cond
      (implies (not (mv-nth 0 (parse-cpp-capture-list-full open-span parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-capture-list-full open-span parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-capture-list-full)
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-read-token-uncond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-cond
                                parsize-of-parse-cpp-type-spec-suffix-uncond
                                parsize-of-parse-cpp-exception-handler-header-uncond
                                parsize-of-parse-cpp-exception-handler-header-cond
                                parsize-of-parse-cpp-param-list-uncond
                                parsize-of-parse-cpp-param-list-cond
                                parsize-of-parse-cpp-capture-list-uncond
                                parsize-of-parse-cpp-capture-list-cond)
             :expand ((parse-cpp-primary parstate)
                      (parse-cpp-arg-list-rest acc parstate)
                      (parse-cpp-postfix-rest lhs lhs-span parstate)
                      (parse-cpp-unary parstate)
                      (parse-cpp-pratt-loop min-prec lhs lhs-span parstate)
                      (parse-cpp-cond-rest test test-span parstate)
                      (parse-cpp-assign-or-cond parstate)
                      (parse-cpp-expr parstate)
                      (parse-cpp-for-opt-test parstate)
                      (parse-cpp-for-opt-next parstate)
                      (parse-cpp-stmt parstate)
                      (parse-cpp-block-item parstate)
                      (parse-cpp-block-item-list-body parstate)
                      (parse-cpp-catch-clause parstate)
                      (parse-cpp-catch-clause-list parstate)
                      (parse-cpp-type-spec-full parstate)
                      (parse-cpp-one-capture-full parstate)
                      (parse-cpp-captures-rest-full acc parstate)
                      (parse-cpp-capture-list-full open-span parstate)))))

  (verify-guards parse-cpp-primary
    :hints (("Goal" :in-theory (enable token-to-cpp-infix-prec
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-type-spec-uncond
                                       parsize-of-parse-cpp-type-spec-cond
                                       parsize-of-parse-cpp-type-spec-full-uncond
                                       parsize-of-parse-cpp-type-spec-full-cond
                                       parsize-of-parse-cpp-type-spec-suffix-uncond
                                       parsize-of-parse-cpp-param-list-uncond
                                       parsize-of-parse-cpp-param-list-cond
                                       parsize-of-parse-cpp-capture-list-full-uncond
                                       parsize-of-parse-cpp-capture-list-full-cond
                                       parsize-of-parse-cpp-exception-handler-header-uncond
                                       parsize-of-parse-cpp-exception-handler-header-cond
                                       parsize-of-parse-cpp-assign-or-cond-uncond
                                       parsize-of-parse-cpp-assign-or-cond-cond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-block ((parstate parstatep))
  :returns (mv erp
               (items cpp-block-item-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ block @('{ body }') and return the body items."
  (b* (((reterr) nil (irr-span) parstate)
       ((erp open? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open? "{"))
        (reterr-msg :where (span->start open-span)
                    :expected "'{' to begin block"
                    :found open?
                    :extra nil))
       ((erp items & parstate) (parse-cpp-block-item-list-body parstate))
       ((erp close? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close? "}"))
        (reterr-msg :where (span->start close-span)
                    :expected "'}' to close block"
                    :found close?
                    :extra nil))
       (span (make-span :start (span->start open-span)
                        :end   (span->end close-span))))
    (retok items span parstate))

  ///

  (defret parsize-of-parse-cpp-block-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper: parse one ctor-init item: ident '(' args ')'.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-ctor-init-item ((parstate parstatep))
  :returns (mv erp
               (item cpp-ctor-init-item-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse one constructor init list item: @('ident ( args )')."
  (b* (((reterr) (irr-cpp-ctor-init-item) (irr-span) parstate)
       ((erp name? name-span parstate) (read-token parstate))
       ((unless (and name? (token-case name? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "identifier in constructor init item"
                    :found name?
                    :extra nil))
       (name-ident (token-ident->ident name?))
       ((erp open? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open? "("))
        (reterr-msg :where (span->start open-span)
                    :expected "'(' in constructor init item"
                    :found open?
                    :extra nil))
       ((erp args close-span parstate) (parse-cpp-arg-list-rest nil parstate))
       (span (make-span :start (span->start name-span)
                        :end   (span->end close-span))))
    (retok (make-cpp-ctor-init-item :name name-ident :bracep nil :args args)
           span parstate))
  ///
  (defret parsize-of-parse-cpp-ctor-init-item-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token))))
  (defret parsize-of-parse-cpp-ctor-init-item-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper: parse comma-separated ctor-init items.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-ctor-init-list ((acc cpp-ctor-init-listp)
                                  (parstate parstatep))
  :returns (mv erp
               (items cpp-ctor-init-listp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :short "Parse a comma-separated list of constructor init items."
  (b* (((reterr) nil parstate)
       ((erp item & parstate) (parse-cpp-ctor-init-item parstate))
       (acc (append acc (list item)))
       ((erp comma? & parstate) (read-token parstate))
       ((when (token-punctuatorp comma? ","))
        (parse-cpp-ctor-init-list acc parstate))
       (parstate (if comma? (unread-token parstate) parstate)))
    (retok (cpp-ctor-init-list-fix acc) parstate))
  ///
  (defret parsize-of-parse-cpp-ctor-init-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-ctor-init-list acc parstate)
             :in-theory (enable parsize-of-parse-cpp-ctor-init-item-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full member field/method parser: like parse-cpp-member-field-or-method
;; but allows an inline method body @('{ ... }') in place of @(';').
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper: parse the body of a constructor or destructor member declaration
;; (params, optional ctor-init-list, then body '{...}' or ';').
;; The caller has already parsed the prefix specifiers and type-spec; the
;; opening '(' of the parameter list is still in the token stream.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-ctor-or-dtor-full
    ((type-spec   cpp-type-spec-p)
     (virtualp    booleanp)
     (staticp     booleanp)
     (destructorp booleanp)
     (explicitp   booleanp)
     (constexprp  booleanp)
     (inlinep     booleanp)
     (start-span  spanp)
     (parstate    parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse the parameter list, optional ctor-init, and body of a
          constructor or destructor."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       (base-ident (if (and (cpp-type-spec-case type-spec :name)
                            (cpp-type-spec-name->id type-spec))
                       (cpp-type-spec-name->id type-spec)
                     (c$::make-ident :unwrap "unknown")))
       (method-id (if destructorp
                      (make-cpp-member-name-destructor :class-name base-ident)
                    (make-cpp-member-name-simple :id base-ident)))
       ((erp params & parstate) (parse-cpp-param-list parstate))
       ((erp const? & parstate) (read-token parstate))
       (const-qualp (token-keywordp const? "const"))
       (parstate (if (and const? (not const-qualp))
                     (unread-token parstate) parstate))
       ;; Optional ctor-init list after ':'
       ((erp colon? & parstate) (read-token parstate))
       ((mv ctor-init-p ctor-init-list parstate)
        (if (token-punctuatorp colon? ":")
            (b* (((mv erp2 items parstate)
                  (parse-cpp-ctor-init-list nil parstate)))
              (if erp2 (mv nil nil parstate) (mv t items parstate)))
          (b* ((parstate (if colon? (unread-token parstate) parstate)))
            (mv nil nil parstate))))
       ;; Body '{' or ';'
       ((erp tail? tail-span parstate) (read-token parstate))
       ((when (token-punctuatorp tail? "{"))
        (b* (((erp body & parstate)
              (parse-cpp-block-item-list-body parstate))
             ((erp close? close-span parstate) (read-token parstate))
             ((unless (token-punctuatorp close? "}"))
              (reterr-msg :where (span->start close-span)
                          :expected "'}'  to close inline body"
                          :found close? :extra nil))
             (span (make-span :start (span->start start-span)
                              :end   (span->end close-span))))
          (retok (make-cpp-member-decl-method
                  :return-type    type-spec
                  :method-id      method-id
                  :params         params
                  :virtualp       virtualp
                  :const-qualp    const-qualp
                  :noexcept-spec  nil
                  :pure-virtualp  nil
                  :staticp        staticp
                  :body-p         t
                  :body           body
                  :destructorp    destructorp
                  :explicitp      explicitp
                  :constexprp     constexprp
                  :inlinep        inlinep
                  :ctor-init-p    ctor-init-p
                  :ctor-init-list ctor-init-list)
                 span parstate)))
       ((unless (token-punctuatorp tail? ";"))
        (reterr-msg :where (span->start tail-span)
                    :expected "';' or '{' after constructor/destructor header"
                    :found tail? :extra nil))
       (span (make-span :start (span->start start-span)
                        :end   (span->end tail-span))))
    (retok (make-cpp-member-decl-method
            :return-type    type-spec
            :method-id      method-id
            :params         params
            :virtualp       virtualp
            :const-qualp    const-qualp
            :noexcept-spec  nil
            :pure-virtualp  nil
            :staticp        staticp
            :body-p         nil
            :body           nil
            :destructorp    destructorp
            :explicitp      explicitp
            :constexprp     constexprp
            :inlinep        inlinep
            :ctor-init-p    ctor-init-p
            :ctor-init-list ctor-init-list)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-member-ctor-or-dtor-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-param-list-uncond
                                parsize-of-parse-cpp-ctor-init-list-uncond))))

  (defret parsize-of-parse-cpp-member-ctor-or-dtor-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-param-list-cond)))))
