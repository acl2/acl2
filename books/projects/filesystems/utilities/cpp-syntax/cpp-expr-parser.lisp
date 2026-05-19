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
;; Mutual recursion for C++ expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ranks (lexicographic with parsize):
;   parse-cpp-primary             : rank 0  (may recurse via '(' expr ')')
;   parse-cpp-arg-list-rest       : rank 0  (called after '(' or ',')
;   parse-cpp-postfix-rest        : rank 0  (called after first primary)
;   parse-cpp-unary               : rank 1  (prefix op self-recursion)
;   parse-cpp-pratt-loop          : rank 2  (consumes op + rhs each iteration)
;   parse-cpp-cond-rest           : rank 3  (consumes '?' first)
;   parse-cpp-assign-or-cond      : rank 4  (consumes first unary)
;   parse-cpp-expr                : rank 5  (top-level; comma)

(defines parse-cpp-expr-mutual
  :parents (parser)

  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-unread-token)))

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
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; this
         ((when (token-cpp-kw-p tok? "this"))
          (retok (cpp-expr-this) tok-span parstate))
         ;; identifier, possibly scoped (A::B::C)
         ((when (and tok? (token-case tok? :ident)))
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
         ;; Lambda stub: '[' opens a lambda capture list — not yet supported
         ((when (token-punctuatorp tok? "["))
          (reterr-msg :where (span->start tok-span)
                      :expected "expression (lambda expressions not yet supported)"
                      :found tok?
                      :extra nil))
         ;; C++ named cast: static_cast<T>(e)
         ((when (token-cpp-kw-p tok? "static_cast"))
          (b* (((erp lt? lt-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lt? "<"))
                (reterr-msg :where (span->start lt-span)
                            :expected "'<' after 'static_cast'"
                            :found lt?
                            :extra nil))
               ((erp type & parstate) (parse-cpp-type-spec parstate))
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
               (psize (parsize parstate))
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
               ((erp type & parstate) (parse-cpp-type-spec parstate))
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
               (psize (parsize parstate))
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
               ((erp type & parstate) (parse-cpp-type-spec parstate))
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
               (psize (parsize parstate))
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
               ((erp type & parstate) (parse-cpp-type-spec parstate))
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
               (psize (parsize parstate))
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
         ;; typeid(T) — always treats argument as a type
         ((when (token-cpp-kw-p tok? "typeid"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'typeid'"
                            :found lp?
                            :extra nil))
               ((erp type & parstate) (parse-cpp-type-spec parstate))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after type in typeid"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-expr-typeid-type :type type) span parstate))))
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
         ;; '.' member
         ((when (token-punctuatorp tok? "."))
          (b* (((erp name? name-span parstate) (read-token parstate))
               ((unless (and name? (token-case name? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "identifier after '.'"
                            :found name?
                            :extra nil))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end name-span)))
               (new-lhs (make-cpp-expr-member
                         :object lhs
                         :name (token-ident->ident name?))))
            (parse-cpp-postfix-rest new-lhs span parstate)))
         ;; '->' member-pointer
         ((when (token-punctuatorp tok? "->"))
          (b* (((erp name? name-span parstate) (read-token parstate))
               ((unless (and name? (token-case name? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "identifier after '->'"
                            :found name?
                            :extra nil))
               (span (make-span :start (span->start lhs-span)
                                :end   (span->end name-span)))
               (new-lhs (make-cpp-expr-memberp
                         :object lhs
                         :name (token-ident->ident name?))))
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
         ((when (token-cpp-kw-p tok? "sizeof"))
          (b* (((erp peek? & parstate) (read-token parstate))
               ;; '(' — could be sizeof(T) or sizeof(expr)
               ((when (token-punctuatorp peek? "("))
                (b* (;; Peek one more token to decide: type keyword or ident?
                     ((erp inner? & parstate) (read-token parstate))
                     ((mv type-first-p parstate)
                      (if (or (and inner? (token-case inner? :keyword))
                              (token-cpp-kw-p inner? "const")
                              (token-cpp-kw-p inner? "volatile"))
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
                      (b* (((erp type & parstate) (parse-cpp-type-spec parstate))
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
               ((erp type & parstate) (parse-cpp-type-spec parstate))
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
          (b* (((erp type type-span parstate) (parse-cpp-type-spec parstate))
               ((erp peek? & parstate) (read-token parstate))
               ((when (token-punctuatorp peek? "("))
                (b* ((psize (parsize parstate))
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
         ;; Otherwise: not a unary prefix — primary followed by postfix
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

  ///

  (defthm-parse-cpp-expr-mutual-flag
    parsize-of-parse-cpp-expr-mutual-uncond
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
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-uncond
                                parse-cpp-primary
                                parse-cpp-arg-list-rest
                                parse-cpp-postfix-rest
                                parse-cpp-unary
                                parse-cpp-pratt-loop
                                parse-cpp-cond-rest
                                parse-cpp-assign-or-cond
                                parse-cpp-expr))))

  (defthm-parse-cpp-expr-mutual-flag
    parsize-of-parse-cpp-expr-mutual-cond
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
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-cond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-type-spec-uncond
                              parsize-of-parse-cpp-type-spec-cond)
                             (mv-nth))
             :expand ((parse-cpp-primary parstate)
                      (parse-cpp-arg-list-rest acc parstate)
                      (parse-cpp-postfix-rest lhs lhs-span parstate)
                      (parse-cpp-unary parstate)
                      (parse-cpp-pratt-loop min-prec lhs lhs-span parstate)
                      (parse-cpp-cond-rest test test-span parstate)
                      (parse-cpp-assign-or-cond parstate)
                      (parse-cpp-expr parstate)))))

  (verify-guards parse-cpp-expr
    :hints (("Goal" :in-theory (enable token-to-cpp-infix-prec
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For-loop helpers: parse optional expression followed by ';' or ')'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parses "[expr] ;" — the test (or init-without-init) slot of a for-loop.
;; If the first token is ';', returns present-p=nil and consumes just ';'.
;; Otherwise unread, parses a full expression, then expects ';'.
(define parse-cpp-for-opt-test ((parstate parstatep))
  :returns (mv erp
               (present-p booleanp)
               (expr cpp-expr-p)
               (new-parstate parstatep :hyp (parstatep parstate)))
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
    (retok t te parstate))
  ///
  (defret parsize-of-parse-cpp-for-opt-test-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-uncond))))
  (defret parsize-of-parse-cpp-for-opt-test-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-cond
                                parsize-of-parse-cpp-expr-uncond)))))

;; Parses "[expr] )" — the next (increment) slot of a for-loop.
;; If the first token is ')', returns present-p=nil and consumes just ')'.
;; Otherwise unread, parses a full expression, then expects ')'.
(define parse-cpp-for-opt-next ((parstate parstatep))
  :returns (mv erp
               (present-p booleanp)
               (expr cpp-expr-p)
               (new-parstate parstatep :hyp (parstatep parstate)))
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
    (retok t ne parstate))
  ///
  (defret parsize-of-parse-cpp-for-opt-next-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-uncond))))
  (defret parsize-of-parse-cpp-for-opt-next-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-cond
                                parsize-of-parse-cpp-expr-uncond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mutual recursion for C++ statements and block items
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Ranks:
;   parse-cpp-stmt                   : rank 0
;   parse-cpp-block-item             : rank 1
;   parse-cpp-block-item-list-body   : rank 2
;   parse-cpp-catch-clause           : rank 3
;   parse-cpp-catch-clause-list      : rank 4

(defines parse-cpp-stmt-mutual
  :parents (parser)

  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-unread-token
                                     parsize-of-parse-cpp-expr-cond
                                     parsize-of-parse-cpp-expr-uncond
                                     parsize-of-parse-cpp-for-opt-test-cond
                                     parsize-of-parse-cpp-for-opt-test-uncond
                                     parsize-of-parse-cpp-for-opt-next-cond
                                     parsize-of-parse-cpp-for-opt-next-uncond)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Parse one C++ statement.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define parse-cpp-stmt ((parstate parstatep))
    :returns (mv erp
                 (stmt cpp-stmt-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 0)
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
         ((when (token-cpp-kw-p tok? "return"))
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
         ((when (token-cpp-kw-p tok? "break"))
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
         ((when (token-cpp-kw-p tok? "continue"))
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
         ((when (token-cpp-kw-p tok? "goto"))
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
         ;; 'if' '(' expr ')' stmt [ 'else' stmt ]
         ((when (token-cpp-kw-p tok? "if"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
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
               ((erp then then-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp e? & parstate) (read-token parstate))
               ((when (token-cpp-kw-p e? "else"))
                (b* (((erp else else-span parstate)
                      (parse-cpp-stmt parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
                      (reterr :impossible))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end else-span))))
                  (retok (make-cpp-stmt-if-else
                          :test test :then then :else else)
                         span parstate)))
               (parstate (if e? (unread-token parstate) parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end then-span))))
            (retok (make-cpp-stmt-if-then :test test :then then)
                   span parstate)))
         ;; 'while' '(' expr ')' stmt
         ((when (token-cpp-kw-p tok? "while"))
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
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end body-span))))
            (retok (make-cpp-stmt-while :test test :body body)
                   span parstate)))
         ;; 'do' stmt 'while' '(' expr ')' ';'
         ((when (token-cpp-kw-p tok? "do"))
          (b* (((erp body & parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ((erp wh? wh-span parstate) (read-token parstate))
               ((unless (token-cpp-kw-p wh? "while"))
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
         ((when (token-cpp-kw-p tok? "switch"))
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
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end body-span))))
            (retok (make-cpp-stmt-switch :target test :body body)
                   span parstate)))
         ;; 'case' expr ':' stmt
         ((when (token-cpp-kw-p tok? "case"))
          (b* (((erp e & parstate) (parse-cpp-assign-or-cond parstate))
               ((erp colon? colon-span parstate) (read-token parstate))
               ((unless (token-punctuatorp colon? ":"))
                (reterr-msg :where (span->start colon-span)
                            :expected "':' after case label"
                            :found colon?
                            :extra nil))
               ((erp s s-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end s-span))))
            (retok (make-cpp-stmt-caselbl :e e :s s) span parstate)))
         ;; 'default' ':' stmt
         ((when (token-cpp-kw-p tok? "default"))
          (b* (((erp colon? colon-span parstate) (read-token parstate))
               ((unless (token-punctuatorp colon? ":"))
                (reterr-msg :where (span->start colon-span)
                            :expected "':' after 'default'"
                            :found colon?
                            :extra nil))
               ((erp s s-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
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
               ((unless (mbt (<= (parsize parstate) psize2)))
                (reterr :impossible))
               ((erp rb? rb-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rb? "}"))
                (reterr-msg :where (span->start rb-span)
                            :expected "'}' to close try body"
                            :found rb?
                            :extra nil))
               ;; parsize < psize because we've consumed '{' and '}' at minimum
               ((unless (mbt (< (parsize parstate) psize)))
                (reterr :impossible))
               ((erp handlers close-span parstate)
                (parse-cpp-catch-clause-list parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end close-span))))
            (retok (make-cpp-stmt-try :body body :handlers handlers)
                   span parstate)))
         ;; 'for' '(' <init> ; <test> ; <next> ')' stmt
         ;;      or 'for' '(' type name : range ')' stmt
         ((when (token-cpp-kw-p tok? "for"))
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
                     ((erp next-p next-e parstate)
                      (parse-cpp-for-opt-next parstate))
                     ((erp body body-span parstate) (parse-cpp-stmt parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
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
                        (token-cpp-kw-p f1? "const")
                        (token-cpp-kw-p f1? "volatile"))
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
                (b* (((erp type & parstate) (parse-cpp-type-spec parstate))
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
                      (b* (((erp range & parstate) (parse-cpp-expr parstate))
                           ((erp rp? rp-span parstate) (read-token parstate))
                           ((unless (token-punctuatorp rp? ")"))
                            (reterr-msg
                             :where (span->start rp-span)
                             :expected "')' after for-range initializer"
                             :found rp?
                             :extra nil))
                           ((erp body body-span parstate)
                            (parse-cpp-stmt parstate))
                           ((unless (mbt (<= (parsize parstate) psize)))
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
                        (b* (((mv erp3 ie & parstate)
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
                     ((erp test-p test-e parstate)
                      (parse-cpp-for-opt-test parstate))
                     ((erp next-p next-e parstate)
                      (parse-cpp-for-opt-next parstate))
                     ((erp body body-span parstate) (parse-cpp-stmt parstate))
                     ((unless (mbt (<= (parsize parstate) psize)))
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
               ((erp test-p test-e parstate)
                (parse-cpp-for-opt-test parstate))
               ((erp next-p next-e parstate)
                (parse-cpp-for-opt-next parstate))
               ((erp body body-span parstate) (parse-cpp-stmt parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
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
               ((unless (mbt (<= (parsize parstate) psize)))
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
    :measure (two-nats-measure (parsize parstate) 1)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-block-item) (irr-span) parstate)
         ((erp t1? t1-span parstate) (read-token parstate))
         ;; Detect "type" prefix: const, volatile, or a C built-in
         ;; type keyword.
         (declp-kw (or (token-cpp-kw-p t1? "const")
                       (token-cpp-kw-p t1? "volatile")
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
                       (token-cpp-kw-p t1? "auto")))
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
          (b* (((erp type & parstate) (parse-cpp-type-spec parstate))
               ((erp name? name-span parstate) (read-token parstate))
               ((unless (and name? (token-case name? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "name in local declaration"
                            :found name?
                            :extra nil))
               ((erp peek? & parstate) (read-token parstate))
               ((mv init-p init parstate)
                (cond ((token-punctuatorp peek? "=")
                       (b* (((mv erp2 e & parstate)
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
    :measure (two-nats-measure (parsize parstate) 2)
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
         ((unless (mbt (< (parsize parstate) psize)))
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
    :measure (two-nats-measure (parsize parstate) 3)
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
    :measure (two-nats-measure (parsize parstate) 4)
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
         ((unless (mbt (< (parsize parstate) psize-list)))
          (reterr :impossible))
         ((erp rest & parstate) (parse-cpp-catch-clause-list parstate)))
      (retok (cons clause rest) peek-span parstate)))

  ///

  (defthm-parse-cpp-stmt-mutual-flag
    parsize-of-parse-cpp-stmt-mutual-uncond
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
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-uncond
                                parsize-of-parse-cpp-expr-cond
                                parsize-of-parse-cpp-assign-or-cond-uncond
                                parsize-of-parse-cpp-assign-or-cond-cond
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-cond
                                parsize-of-parse-cpp-exception-handler-header-uncond
                                parsize-of-parse-cpp-exception-handler-header-cond
                                parsize-of-parse-cpp-for-opt-test-uncond
                                parsize-of-parse-cpp-for-opt-test-cond
                                parsize-of-parse-cpp-for-opt-next-uncond
                                parsize-of-parse-cpp-for-opt-next-cond)
             :expand ((parse-cpp-stmt parstate)
                      (parse-cpp-block-item parstate)
                      (parse-cpp-block-item-list-body parstate)
                      (parse-cpp-catch-clause parstate)
                      (parse-cpp-catch-clause-list parstate)))))

  (defthm-parse-cpp-stmt-mutual-flag
    parsize-of-parse-cpp-stmt-mutual-cond
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
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-expr-uncond
                                parsize-of-parse-cpp-expr-cond
                                parsize-of-parse-cpp-assign-or-cond-uncond
                                parsize-of-parse-cpp-assign-or-cond-cond
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-cond
                                parsize-of-parse-cpp-exception-handler-header-uncond
                                parsize-of-parse-cpp-exception-handler-header-cond
                                parsize-of-parse-cpp-for-opt-test-uncond
                                parsize-of-parse-cpp-for-opt-test-cond
                                parsize-of-parse-cpp-for-opt-next-uncond
                                parsize-of-parse-cpp-for-opt-next-cond)
             :expand ((parse-cpp-stmt parstate)
                      (parse-cpp-block-item parstate)
                      (parse-cpp-block-item-list-body parstate)
                      (parse-cpp-catch-clause parstate)
                      (parse-cpp-catch-clause-list parstate)))))

  (verify-guards parse-cpp-stmt
    :hints (("Goal" :in-theory (enable c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse a top-level C++ compound block: '{' body '}'.
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
;; Full member field/method parser: like parse-cpp-member-field-or-method
;; but allows an inline method body @('{ ... }') in place of @(';').
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-field-or-method-full ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ field or method, possibly with an inline body."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ((erp t1? t1-span parstate) (read-token parstate))
       (virtualp (token-cpp-kw-p t1? "virtual"))
       ((erp t1? t1-span parstate)
        (if virtualp
            (read-token parstate)
          (mv nil t1? t1-span parstate)))
       (staticp (token-cpp-kw-p t1? "static"))
       (mutablep (and (not staticp) (token-cpp-kw-p t1? "mutable")))
       ((erp t1? t1-span parstate)
        (if (or staticp mutablep)
            (read-token parstate)
          (mv nil t1? t1-span parstate)))
       ((unless (and t1? (token-case t1? :ident)))
        (reterr-msg :where (span->start t1-span)
                    :expected "type specifier in member declaration"
                    :found t1?
                    :extra nil))
       (parstate (unread-token parstate))
       ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
       ((erp name? name-span parstate) (read-token parstate))
       ((unless (and name? (token-case name? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "member name identifier"
                    :found name?
                    :extra nil))
       (name-ident (token-ident->ident name?))
       ((erp peek? & parstate) (read-token parstate))
       ;; Field case
       ((when (not (token-punctuatorp peek? "(")))
        (b* ((parstate (if peek? (unread-token parstate) parstate))
             ((erp semi? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after field declaration"
                          :found semi?
                          :extra nil))
             (span (make-span :start (span->start t1-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-field
                  :type-name  type-spec
                  :field-name name-ident
                  :staticp    staticp
                  :mutablep   mutablep)
                 span parstate)))
       ;; Method case
       ((erp params & parstate) (parse-cpp-param-list parstate))
       ((erp const? & parstate) (read-token parstate))
       (const-qualp (token-keywordp const? "const"))
       (parstate (if (and const? (not const-qualp))
                     (unread-token parstate)
                   parstate))
       ((erp noex? & parstate) (read-token parstate))
       (noexcept-p (token-cpp-noexcept-p noex?))
       (parstate (if noex? (unread-token parstate) parstate))
       ((erp noexcept-raw & parstate)
        (if noexcept-p
            (parse-cpp-noexcept-spec parstate)
          (mv nil (irr-cpp-noexcept-spec) (irr-span) parstate)))
       (noexcept-spec (if noexcept-p
                          (cpp-noexcept-spec-option-some noexcept-raw)
                        nil))
       ((erp eq? & parstate) (read-token parstate))
       ((erp zero? & parstate)
        (if (token-punctuatorp eq? "=")
            (read-token parstate)
          (mv nil nil (irr-span) parstate)))
       (pure-virtualp (and (token-punctuatorp eq? "=")
                           zero? (token-case zero? :const)))
       (parstate
        (cond
         (pure-virtualp parstate)
         ((token-punctuatorp eq? "=")
          (let* ((parstate (if zero? (unread-token parstate) parstate))
                 (parstate (unread-token parstate)))
            parstate))
         (t
          (if eq? (unread-token parstate) parstate))))
       ;; Now check for inline body '{' or ';'
       ((erp tail? tail-span parstate) (read-token parstate))
       ;; '{' inline body
       ((when (token-punctuatorp tail? "{"))
        (b* (((erp body & parstate)
              (parse-cpp-block-item-list-body parstate))
             ((erp close? close-span parstate) (read-token parstate))
             ((unless (token-punctuatorp close? "}"))
              (reterr-msg :where (span->start close-span)
                          :expected "'}' to close inline method body"
                          :found close?
                          :extra nil))
             (span (make-span :start (span->start t1-span)
                              :end   (span->end close-span))))
          (retok (make-cpp-member-decl-method
                  :return-type   type-spec
                  :method-name   name-ident
                  :params        params
                  :virtualp      virtualp
                  :const-qualp   const-qualp
                  :noexcept-spec noexcept-spec
                  :pure-virtualp pure-virtualp
                  :staticp       staticp
                  :body-p        t
                  :body          body)
                 span parstate)))
       ;; ';' no body
       ((unless (token-punctuatorp tail? ";"))
        (reterr-msg :where (span->start tail-span)
                    :expected "';' or '{' after method header"
                    :found tail?
                    :extra nil))
       (span (make-span :start (span->start t1-span)
                        :end   (span->end tail-span))))
    (retok (make-cpp-member-decl-method
            :return-type   type-spec
            :method-name   name-ident
            :params        params
            :virtualp      virtualp
            :const-qualp   const-qualp
            :noexcept-spec noexcept-spec
            :pure-virtualp pure-virtualp
            :staticp       staticp
            :body-p        nil
            :body          nil)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-member-field-or-method-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-member-field-or-method-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full member-decl item: access label or field/method (with possible body).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-decl-item-full ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse one C++ class member declaration, allowing inline bodies."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ((erp peek? peek-span parstate) (read-token parstate))
       ((when (token-cpp-access-spec-p peek?))
        (b* ((parstate (unread-token parstate)))
          (parse-cpp-member-access-label parstate)))
       ((unless peek?)
        (reterr-msg :where (span->start peek-span)
                    :expected "class member declaration or '}'"
                    :found peek?
                    :extra nil))
       (parstate (unread-token parstate)))
    (parse-cpp-member-field-or-method-full parstate))

  ///

  (defret parsize-of-parse-cpp-member-decl-item-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-member-decl-item-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :use ((:instance parsize-of-parse-cpp-member-access-label-cond)
                   (:instance parsize-of-parse-cpp-member-field-or-method-full-cond))
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full member-decl list body.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-decl-list-body-full ((parstate parstatep))
  :returns (mv erp
               (decls cpp-member-decl-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :short "Parse a sequence of C++ class member declarations until @('}')."
  (b* (((reterr) nil (irr-span) parstate)
       ((erp peek? peek-span parstate) (read-token parstate))
       ((when (or (not peek?)
                  (token-punctuatorp peek? "}")))
        (b* ((parstate (if peek? (unread-token parstate) parstate)))
          (retok nil peek-span parstate)))
       (parstate (unread-token parstate))
       ((erp decl decl-span parstate) (parse-cpp-member-decl-item-full parstate))
       ((erp rest & parstate) (parse-cpp-member-decl-list-body-full parstate)))
    (retok (cons decl rest) decl-span parstate))

  ///

  (defret parsize-of-parse-cpp-member-decl-list-body-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-member-decl-list-body-full parstate)
             :in-theory (enable parsize-of-parse-cpp-member-decl-item-full-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full class specifier: like parse-cpp-class-specifier, but its members
;; can have inline bodies.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-class-specifier-full ((parstate parstatep))
  :returns (mv erp
               (cls cpp-class-specifier-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ class specifier whose members may have inline bodies."
  (b* (((reterr) (irr-cpp-class-specifier) (irr-span) parstate)
       ((erp key key-span parstate) (parse-cpp-class-key parstate))
       ((erp name? & parstate) (read-token parstate))
       (name-p (and name?
                    (token-case name? :ident)
                    (not (token-punctuatorp name? "{"))
                    (not (token-punctuatorp name? "<"))
                    (not (token-punctuatorp name? ":"))))
       (class-name (if name-p (token-ident->ident name?) nil))
       (parstate (if (and name? (not name-p))
                     (unread-token parstate)
                   parstate))
       ((erp tmpl? & parstate) (read-token parstate))
       ((mv template-params parstate)
        (cond
         ((token-punctuatorp tmpl? "<")
          (b* ((parstate (unread-token parstate))
               ((mv erp2 params & parstate)
                (parse-cpp-template-param-list parstate)))
            (if erp2 (mv nil parstate) (mv params parstate))))
         (tmpl?
          (let* ((parstate (unread-token parstate)))
            (mv nil parstate)))
         (t (mv nil parstate))))
       ((erp colon? & parstate) (read-token parstate))
       ((mv bases parstate)
        (cond
         ((token-punctuatorp colon? ":")
          (b* ((parstate (unread-token parstate))
               ((mv erp2 base-list & parstate)
                (parse-cpp-base-clause parstate)))
            (if erp2 (mv nil parstate) (mv base-list parstate))))
         (colon?
          (let* ((parstate (unread-token parstate)))
            (mv nil parstate)))
         (t (mv nil parstate))))
       ((erp open? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open? "{"))
        (reterr-msg :where (span->start open-span)
                    :expected "'{' to begin class body"
                    :found open?
                    :extra nil))
       ((erp members & parstate)
        (parse-cpp-member-decl-list-body-full parstate))
       ((erp close? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close? "}"))
        (reterr-msg :where (span->start close-span)
                    :expected "'}' to end class body"
                    :found close?
                    :extra nil))
       (span (make-span :start (span->start key-span)
                        :end   (span->end close-span))))
    (retok (make-cpp-class-specifier
            :key             key
            :name            class-name
            :template-params template-params
            :base            bases
            :members         members)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-class-specifier-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))
