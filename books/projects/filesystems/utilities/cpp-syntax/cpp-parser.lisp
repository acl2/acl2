; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines recursive-descent parse functions for C++ constructs.
; The functions operate on the same parstate stobj used by the C$ parser,
; returning (mv erp result span new-parstate) tuples.
;
; Parse functions defined here:
;  - parse-cpp-access-specifier       (public/private/protected)
;  - parse-cpp-operator-function-id   (operator +, operator[], etc.)
;  - parse-cpp-template-param         (typename T, int N, etc.)
;  - parse-cpp-template-param-list    (< T1, T2, ... >)
;  - parse-cpp-namespace-def-header   (namespace [Name] or namespace A::B)
;  - parse-cpp-class-key              (class or struct)
;  - parse-cpp-base-specifier         ([access] class-name)
;  - parse-cpp-base-clause            (: base-spec {, base-spec}*)
;  - parse-cpp-member-access-label    (access :)
;  - parse-cpp-member-field-or-method ([virtual][static] type name [(...)] [const] [noexcept] [=0] ;)
;  - parse-cpp-member-decl-item       (one member: access-label or field/method)
;  - parse-cpp-member-decl-list-body  (list of members until '}')
;  - parse-cpp-class-specifier        (class-head { members }, no inline bodies)
;  - parse-cpp-noexcept-spec          (noexcept [(true/false)])
;  - parse-cpp-exception-handler-header (catch ( type [name] ))
;  - parse-cpp-exception-handler-list (list of catch headers)
;  - parse-cpp-module-decl-header     ([export] module [name])
;  - parse-cpp-import-decl-header     ([export] import name)
;  - parse-cpp-type-spec              (type specifiers, recursive)
;  - parse-cpp-param-list             (( type [name] {, type [name]}* ))
;  - parse-cpp-using-decl             (using / using alias)
;  - parse-cpp-enum-decl              (enum / enum class with enumerators)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-abstract-syntax")
(include-book "cpp-token-utilities")

(include-book "kestrel/c/syntax/lexer" :dir :system)
(include-book "kestrel/c/syntax/parser-messages" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cpp-parser
  :parents (cpp-syntax)
  :short "Recursive-descent parser for C++ constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define functions to parse C++ constructs from the parser state
     @(tsee c$::parstate).
     Each function follows the same interface as the C$ parser functions:
     it takes a parser state and returns
     @('(mv erp result span new-parstate)').")
   (xdoc::p
    "Since C++ keywords arrive as @(see c$::token-ident) tokens
     (because the C$ lexer does not know about C++ keywords),
     our parse functions use @(tsee token-cpp-kw-p) for keyword checks
     rather than @(tsee c$::token-keywordp).")
   (xdoc::p
    "All recursive functions use @('(parsize parstate)') as the termination
     measure.
     Each call to @(tsee c$::read-token) that consumes a token strictly
     decreases @('(parsize parstate)'), ensuring termination."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Mapping tokens to AST nodes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-access-spec ((token? token-optionp))
  :guard (token-cpp-access-spec-p token?)
  :returns (spec cpp-access-spec-p)
  :short "Map an access-specifier token to the corresponding fixtype variant."
  (cond ((token-cpp-kw-p token? "public")    (cpp-access-spec-public))
        ((token-cpp-kw-p token? "private")   (cpp-access-spec-private))
        ((token-cpp-kw-p token? "protected") (cpp-access-spec-protected))
        (t (prog2$ (impossible) (irr-cpp-access-spec))))
  :prepwork ((local (in-theory (enable token-cpp-access-spec-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-class-key ((token? token-optionp))
  :guard (token-cpp-class-key-p token?)
  :returns (key cpp-class-key-p)
  :short "Map a class-key token to the corresponding fixtype variant."
  (cond ((token-cpp-kw-p token? "class")    (cpp-class-key-class))
        ((token-keywordp token? "struct")   (cpp-class-key-struct))
        (t (prog2$ (impossible) (cpp-class-key-class))))
  :prepwork ((local (in-theory (enable token-cpp-class-key-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-operator-kind ((token? token-optionp))
  :guard (token-cpp-overloadable-op-p token?)
  :returns (op cpp-operator-kind-p)
  :short "Map an overloadable-operator token to the corresponding operator kind."
  (cond
   ;; Arithmetic
   ((token-punctuatorp token? "+")   (cpp-operator-kind-plus))
   ((token-punctuatorp token? "-")   (cpp-operator-kind-minus))
   ((token-punctuatorp token? "*")   (cpp-operator-kind-star))
   ((token-punctuatorp token? "/")   (cpp-operator-kind-slash))
   ((token-punctuatorp token? "%")   (cpp-operator-kind-percent))
   ;; Bitwise
   ((token-punctuatorp token? "^")   (cpp-operator-kind-caret))
   ((token-punctuatorp token? "&")   (cpp-operator-kind-amp))
   ((token-punctuatorp token? "|")   (cpp-operator-kind-pipe))
   ((token-punctuatorp token? "~")   (cpp-operator-kind-tilde))
   ;; Logical
   ((token-punctuatorp token? "!")   (cpp-operator-kind-bang))
   ((token-punctuatorp token? "&&")  (cpp-operator-kind-amp-amp))
   ((token-punctuatorp token? "||")  (cpp-operator-kind-pipe-pipe))
   ;; Shift
   ((token-punctuatorp token? "<<")  (cpp-operator-kind-lshift))
   ((token-punctuatorp token? ">>")  (cpp-operator-kind-rshift))
   ;; Comparison
   ((token-punctuatorp token? "==")  (cpp-operator-kind-eq))
   ((token-punctuatorp token? "!=")  (cpp-operator-kind-ne))
   ((token-punctuatorp token? "<")   (cpp-operator-kind-lt))
   ((token-punctuatorp token? ">")   (cpp-operator-kind-gt))
   ((token-punctuatorp token? "<=")  (cpp-operator-kind-le))
   ((token-punctuatorp token? ">=")  (cpp-operator-kind-ge))
   ((token-punctuatorp token? "<=>") (cpp-operator-kind-spaceship))
   ;; Assignment
   ((token-punctuatorp token? "=")   (cpp-operator-kind-asg))
   ((token-punctuatorp token? "+=")  (cpp-operator-kind-plus-asg))
   ((token-punctuatorp token? "-=")  (cpp-operator-kind-minus-asg))
   ((token-punctuatorp token? "*=")  (cpp-operator-kind-star-asg))
   ((token-punctuatorp token? "/=")  (cpp-operator-kind-slash-asg))
   ((token-punctuatorp token? "%=")  (cpp-operator-kind-percent-asg))
   ((token-punctuatorp token? "^=")  (cpp-operator-kind-caret-asg))
   ((token-punctuatorp token? "&=")  (cpp-operator-kind-amp-asg))
   ((token-punctuatorp token? "|=")  (cpp-operator-kind-pipe-asg))
   ((token-punctuatorp token? "<<=") (cpp-operator-kind-lshift-asg))
   ((token-punctuatorp token? ">>=") (cpp-operator-kind-rshift-asg))
   ;; Increment / decrement
   ((token-punctuatorp token? "++")  (cpp-operator-kind-inc))
   ((token-punctuatorp token? "--")  (cpp-operator-kind-dec))
   ;; Access operators
   ((token-punctuatorp token? "->")  (cpp-operator-kind-arrow))
   ((token-punctuatorp token? "->*") (cpp-operator-kind-arrow-star))
   ;; Comma
   ((token-punctuatorp token? ",")   (cpp-operator-kind-comma))
   ;; Memory management (arrive as identifiers)
   ((token-cpp-kw-p token? "new")    (cpp-operator-kind-new))
   ((token-cpp-kw-p token? "delete") (cpp-operator-kind-delete))
   ;; Coroutines
   ((token-cpp-kw-p token? "co_await") (cpp-operator-kind-co-await))
   ;; Fallthrough — logically unreachable under the guard
   (t (prog2$ (impossible) (cpp-operator-kind-plus))))
  :prepwork ((local (in-theory (enable token-cpp-overloadable-op-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-coroutine-kw-kind ((token? token-optionp))
  :guard (token-cpp-coroutine-kw-p token?)
  :verify-guards nil
  :returns (kind cpp-coroutine-kw-kind-p)
  :short "Map a coroutine-keyword token to the corresponding @(tsee cpp-coroutine-kw-kind)."
  (cond ((token-cpp-kw-p token? "co_return") (cpp-coroutine-kw-kind-return))
        ((token-cpp-kw-p token? "co_yield")  (cpp-coroutine-kw-kind-yield))
        (t                                   (cpp-coroutine-kw-kind-await)))
  :prepwork ((local (in-theory (enable token-cpp-coroutine-kw-p))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Access Specifier
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-access-specifier ((parstate parstatep))
  :returns (mv erp
               (spec cpp-access-spec-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ access specifier: @('public'), @('private'), or @('protected')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads one token.
     If it is an identifier whose name is one of
     @('public'), @('private'), or @('protected'),
     returns the corresponding @(tsee cpp-access-spec) variant.
     Otherwise, returns an error."))
  (b* (((reterr) (irr-cpp-access-spec) (irr-span) parstate)
       ((erp token? span parstate) (read-token parstate))
       ((unless (token-cpp-access-spec-p token?))
        (reterr-msg :where (span->start span)
                    :expected "access specifier (public / private / protected)"
                    :found token?
                    :extra nil)))
    (retok (token-to-cpp-access-spec token?) span parstate))

  ///

  (defret parsize-of-parse-cpp-access-specifier-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :use (:instance c$::parsize-of-read-token-uncond
                                    (parstate parstate)))))

  (defret parsize-of-parse-cpp-access-specifier-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :use (:instance c$::parsize-of-read-token-cond
                                    (parstate parstate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Class Key
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-class-key ((parstate parstatep))
  :returns (mv erp
               (key cpp-class-key-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ class key: @('class') or @('struct')."
  (b* (((reterr) (cpp-class-key-class) (irr-span) parstate)
       ((erp token? span parstate) (read-token parstate))
       ((unless (token-cpp-class-key-p token?))
        (reterr-msg :where (span->start span)
                    :expected "class key (class / struct)"
                    :found token?
                    :extra nil)))
    (retok (token-to-cpp-class-key token?) span parstate))

  ///

  (defret parsize-of-parse-cpp-class-key-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :use (:instance c$::parsize-of-read-token-uncond
                                    (parstate parstate)))))

  (defret parsize-of-parse-cpp-class-key-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :use (:instance c$::parsize-of-read-token-cond
                                    (parstate parstate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Operator Function Id
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-operator-function-id ((parstate parstatep))
  :returns (mv erp
               (op-id cpp-operator-function-id-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ operator function identifier: @('operator OP')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses @('operator') (arriving as an identifier token)
     followed by the operator symbol.")
   (xdoc::p
    "The call operator @('operator()') and subscript operator @('operator[]')
     each require two consecutive punctuator tokens.
     For @('operator()'), we read @('(') then @(')').
     For @('operator[]'), we read @('[') then @(']').
     For all other operators, a single token suffices.")
   (xdoc::p
    "For @('operator new[]') and @('operator delete[]'),
     we read the keyword followed by @('[') and @(']')."))
  (b* (((reterr) (irr-cpp-operator-function-id) (irr-span) parstate)
       ;; Read the 'operator' keyword (arrives as identifier)
       ((erp op-token? op-span parstate) (read-token parstate))
       ((unless (token-cpp-kw-p op-token? "operator"))
        (reterr-msg :where (span->start op-span)
                    :expected "'operator' keyword"
                    :found op-token?
                    :extra nil))
       ;; Read the operator symbol
       ((erp sym-token? sym-span parstate) (read-token parstate))
       ;; Handle operator() and operator[]
       ((when (token-punctuatorp sym-token? "("))
        ;; Expect a closing ')'
        (b* (((erp close-token? close-span parstate) (read-token parstate))
             ((unless (token-punctuatorp close-token? ")"))
              (reterr-msg :where (span->start close-span)
                          :expected "')' after 'operator('"
                          :found close-token?
                          :extra nil))
             (span (make-span :start (span->start op-span)
                              :end   (span->end close-span))))
          (retok (make-cpp-operator-function-id :op (cpp-operator-kind-call))
                 span parstate)))
       ((when (token-punctuatorp sym-token? "["))
        ;; Expect a closing ']'
        (b* (((erp close-token? close-span parstate) (read-token parstate))
             ((unless (token-punctuatorp close-token? "]"))
              (reterr-msg :where (span->start close-span)
                          :expected "']' after 'operator['"
                          :found close-token?
                          :extra nil))
             (span (make-span :start (span->start op-span)
                              :end   (span->end close-span))))
          (retok (make-cpp-operator-function-id :op (cpp-operator-kind-subscript))
                 span parstate)))
       ;; Handle operator new[] and operator delete[]
       ((when (token-cpp-kw-p sym-token? "new"))
        (b* (;; Check for 'new[]'
             ((erp maybe-bracket? & parstate) (read-token parstate))
             ((when (token-punctuatorp maybe-bracket? "["))
              (b* (((erp close-token? close-span parstate)
                    (read-token parstate))
                   ((unless (token-punctuatorp close-token? "]"))
                    (reterr-msg :where (span->start close-span)
                                :expected "']' in 'operator new[]'"
                                :found close-token?
                                :extra nil))
                   (span (make-span :start (span->start op-span)
                                    :end   (span->end close-span))))
                (retok (make-cpp-operator-function-id
                        :op (cpp-operator-kind-new-array))
                       span parstate)))
             ;; Plain operator new — unread the non-bracket token
             (parstate (if maybe-bracket? (unread-token parstate) parstate))
             (span (make-span :start (span->start op-span)
                              :end   (span->end sym-span))))
          (retok (make-cpp-operator-function-id :op (cpp-operator-kind-new))
                 span parstate)))
       ((when (token-cpp-kw-p sym-token? "delete"))
        (b* (;; Check for 'delete[]'
             ((erp maybe-bracket? & parstate) (read-token parstate))
             ((when (token-punctuatorp maybe-bracket? "["))
              (b* (((erp close-token? close-span parstate)
                    (read-token parstate))
                   ((unless (token-punctuatorp close-token? "]"))
                    (reterr-msg :where (span->start close-span)
                                :expected "']' in 'operator delete[]'"
                                :found close-token?
                                :extra nil))
                   (span (make-span :start (span->start op-span)
                                    :end   (span->end close-span))))
                (retok (make-cpp-operator-function-id
                        :op (cpp-operator-kind-delete-array))
                       span parstate)))
             ;; Plain operator delete — unread non-bracket token
             (parstate (if maybe-bracket? (unread-token parstate) parstate))
             (span (make-span :start (span->start op-span)
                              :end   (span->end sym-span))))
          (retok (make-cpp-operator-function-id :op (cpp-operator-kind-delete))
                 span parstate)))
       ;; All other operators: a single punctuator or co_await
       ((unless (token-cpp-overloadable-op-p sym-token?))
        (reterr-msg :where (span->start sym-span)
                    :expected "overloadable operator after 'operator'"
                    :found sym-token?
                    :extra nil))
       (op-kind (token-to-cpp-operator-kind sym-token?))
       (span (make-span :start (span->start op-span)
                        :end   (span->end sym-span))))
    (retok (make-cpp-operator-function-id :op op-kind) span parstate))

  ///

  (defret parsize-of-parse-cpp-operator-function-id-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Type Specifier
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: parse the suffix (pointer / reference) after a base type spec
(define parse-cpp-type-spec-suffix ((base cpp-type-spec-p)
                                    (base-span spanp)
                                    (parstate parstatep))
  :returns (mv erp
               (spec cpp-type-spec-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse optional pointer/reference suffixes after a base type."
  :long
  (xdoc::topstring
   (xdoc::p
    "After parsing the base of a type, peek for @('*'), @('&'), or @('&&').
     If @('*'), also check for @('const') after it."))
  (b* (((reterr) (irr-cpp-type-spec) (irr-span) parstate)
       ;; Peek at the next token
       ((erp peek-token? peek-span parstate) (read-token parstate))
       ;; Pointer: *
       ((when (token-punctuatorp peek-token? "*"))
        (b* (;; Check for 'const' after '*'
             ((erp const-tok? const-span parstate) (read-token parstate))
             (constp (token-keywordp const-tok? "const"))
             (parstate (if (and const-tok? (not constp))
                           (unread-token parstate)
                         parstate))
             (end-span (if constp const-span peek-span))
             (span (make-span :start (span->start base-span)
                              :end   (span->end end-span))))
          (retok (make-cpp-type-spec-pointer :pointee (cpp-type-spec-fix base)
                                             :constp constp)
                 span parstate)))
       ;; Reference: & or &&
       ((when (token-punctuatorp peek-token? "&&"))
        (b* ((span (make-span :start (span->start base-span)
                              :end   (span->end peek-span))))
          (retok (make-cpp-type-spec-rref :base (cpp-type-spec-fix base))
                 span parstate)))
       ((when (token-punctuatorp peek-token? "&"))
        (b* ((span (make-span :start (span->start base-span)
                              :end   (span->end peek-span))))
          (retok (make-cpp-type-spec-lref :base (cpp-type-spec-fix base))
                 span parstate)))
       ;; No suffix — put back and return base
       ;; Array: '[' [']' | ident ']' | integer-const ']']
       ((when (token-punctuatorp peek-token? "["))
        (b* (((erp inner? inner-span parstate) (read-token parstate))
             ;; Unsized array: T[]
             ((when (token-punctuatorp inner? "]"))
              (b* ((span (make-span :start (span->start base-span)
                                    :end   (span->end inner-span))))
                (retok (make-cpp-type-spec-array :element (cpp-type-spec-fix base)
                                                 :size-p nil
                                                 :size (irr-cpp-const-expr))
                       span parstate)))
             ;; Sized array: T[N] where N is an identifier (named constant)
             ((when (and inner? (token-case inner? :ident)))
              (b* ((size-ident (make-cpp-const-expr-ident
                                :name (token-ident->ident inner?)))
                   ((erp rb? rb-span parstate) (read-token parstate))
                   ((unless (token-punctuatorp rb? "]"))
                    (reterr-msg :where (span->start rb-span)
                                :expected "']' after named array size"
                                :found rb?
                                :extra nil))
                   (span (make-span :start (span->start base-span)
                                    :end   (span->end rb-span))))
                (retok (make-cpp-type-spec-array :element (cpp-type-spec-fix base)
                                                 :size-p t
                                                 :size size-ident)
                       span parstate)))
             ;; Sized array: T[N] where N is an integer constant
             ((unless (and inner? (token-case inner? :const)
                           (c$::const-case (c$::token-const->const inner?) :int)))
              (reterr-msg :where (span->start inner-span)
                          :expected "integer constant, identifier, or ']' in array size"
                          :found inner?
                          :extra nil))
             (size-const (make-cpp-const-expr-int
                          :iconst (c$::const-int->iconst (c$::token-const->const inner?))))
             ((erp rb? rb-span parstate) (read-token parstate))
             ((unless (token-punctuatorp rb? "]"))
              (reterr-msg :where (span->start rb-span)
                          :expected "']' after array size"
                          :found rb?
                          :extra nil))
             (span (make-span :start (span->start base-span)
                              :end   (span->end rb-span))))
          (retok (make-cpp-type-spec-array :element (cpp-type-spec-fix base)
                                           :size-p t
                                           :size size-const)
                 span parstate)))
       ;; No suffix — put back and return base
       (parstate (if peek-token? (unread-token parstate) parstate)))
    (retok (cpp-type-spec-fix base) (span-fix base-span) parstate))

  ///

  (defret parsize-of-parse-cpp-type-spec-suffix-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Main recursive type-spec parser.
;; The mutual recursion between type-spec parsing and template argument
;; list parsing is handled via defines with two-nats-measure.
;; parse-cpp-type-spec-one (rank 1) parses a single type-spec;
;; parse-cpp-type-spec-arg-list-rest (rank 0) parses comma-separated
;; template args until '>'.  mbt assertions capture parsize decrease
;; for cross-calls; :verify-guards :after-returns defers guard proofs
;; so defret lemmas are available.

(defines parse-cpp-type-spec-mutual
  :parents (parser)
  ;; Hint for the auto-generated return-type flag lemma: expand the two
  ;; functions once at Goal (where the induction is set up), then disable
  ;; their definitions so they are not re-expanded in every subgoal.
  :returns-hints (("Goal" :in-theory (e/d () (parse-cpp-type-spec-one
                                              parse-cpp-type-spec-arg-list-rest))
                   :expand ((parse-cpp-type-spec-one parstate)
                            (parse-cpp-type-spec-arg-list-rest acc parstate))))

  ;; parse-cpp-type-spec-one: parse a single type-spec without suffix.
  ;; Reads: [const/volatile] ident [:: ident]* [< args >]
  ;; Does NOT handle pointer/reference suffixes (those are added by caller).
  (define parse-cpp-type-spec-one ((parstate parstatep))
    :returns (mv erp
                 (spec cpp-type-spec-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 1)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-type-spec) (irr-span) parstate)
         ;; Read the first token
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; const qualifier
         ((when (token-keywordp tok? "const"))
          (b* (((erp inner inner-span parstate) (parse-cpp-type-spec-one parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end inner-span))))
            (retok (make-cpp-type-spec-const-qual :base inner)
                   span parstate)))
         ;; volatile qualifier
         ((when (token-keywordp tok? "volatile"))
          (b* (((erp inner inner-span parstate) (parse-cpp-type-spec-one parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end inner-span))))
            (retok (make-cpp-type-spec-volatile-qual :base inner)
                   span parstate)))
         ;; C17 keyword type names: greedily consume combinable type keywords
         ;; to support 'unsigned int', 'long long', 'unsigned long long', etc.
         ((when (and tok? (token-case tok? :keyword)))
          (b* ((kw1 (token-keyword->keyword tok?))
               ;; Try to read a second combinable type keyword
               ((erp k2? k2-span parstate) (read-token parstate))
               ((mv kw-str kw-end-span parstate)
                (if (not (and k2? (token-case k2? :keyword)
                              (member-equal (token-keyword->keyword k2?)
                                            '("unsigned" "signed" "short" "long"
                                              "int" "char" "double" "float"))))
                    ;; No second combinable keyword: put k2? back, single keyword
                    (b* ((parstate (if k2? (unread-token parstate) parstate)))
                      (mv kw1 tok-span parstate))
                  ;; Two-keyword combination: 'unsigned int', 'long long', etc.
                  (b* ((kw2 (token-keyword->keyword k2?))
                       ;; Try a third keyword
                       ((mv erp3 k3? k3-span parstate) (read-token parstate))
                       ((mv kw-str kw-end-span parstate)
                        (if (not (and (not erp3) k3? (token-case k3? :keyword)
                                      (member-equal (token-keyword->keyword k3?)
                                                    '("unsigned" "signed" "short" "long"
                                                      "int" "char" "double" "float"))))
                            ;; Two keywords only: put k3? back
                            (b* ((parstate (if (and (not erp3) k3?)
                                              (unread-token parstate) parstate)))
                              (mv (string-append kw1 (string-append " " kw2))
                                  k2-span parstate))
                          ;; Three-keyword combination: 'unsigned long long', etc.
                          (b* ((kw3 (token-keyword->keyword k3?))
                               ;; Try a fourth keyword
                               ((mv erp4 k4? k4-span parstate) (read-token parstate))
                               ((mv kw-str kw-end-span parstate)
                                (if (not (and (not erp4) k4? (token-case k4? :keyword)
                                              (member-equal (token-keyword->keyword k4?)
                                                            '("unsigned" "signed" "short" "long"
                                                              "int" "char" "double" "float"))))
                                    ;; Three keywords only: put k4? back
                                    (b* ((parstate (if (and (not erp4) k4?)
                                                      (unread-token parstate) parstate)))
                                      (mv (string-append kw1
                                            (string-append " "
                                              (string-append kw2
                                                (string-append " " kw3))))
                                          k3-span parstate))
                                  ;; Four keywords: 'unsigned long long int'
                                  (mv (string-append kw1
                                        (string-append " "
                                          (string-append kw2
                                            (string-append " "
                                              (string-append kw3
                                                (string-append " "
                                                  (token-keyword->keyword k4?)))))))
                                      k4-span parstate))))
                            (mv kw-str kw-end-span parstate)))))
                    (mv kw-str kw-end-span parstate))))
               (id (c$::make-ident :unwrap kw-str))
               (base (make-cpp-type-spec-name :id id))
               ;; Check for '::' after the full (possibly multi-keyword) type
               ((erp sep? & parstate) (read-token parstate))
               ((when (token-punctuatorp sep? "::"))
                (b* (((erp inner inner-span parstate) (parse-cpp-type-spec-one parstate))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end inner-span))))
                  (retok (make-cpp-type-spec-qualified :scope id :inner inner)
                         span parstate)))
               (parstate (if sep? (unread-token parstate) parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end kw-end-span))))
            (retok base span parstate)))
         ;; Must be an identifier
         ((unless (and tok? (token-case tok? :ident)))
          (reterr-msg :where (span->start tok-span)
                      :expected "type name identifier"
                      :found tok?
                      :extra nil))
         (id (token-ident->ident tok?))
         ;; Special case: 'decltype' '(' ident ')'
         ((when (equal (ident->unwrap id) "decltype"))
          (b* (((erp lp? lp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lp? "("))
                (reterr-msg :where (span->start lp-span)
                            :expected "'(' after 'decltype'"
                            :found lp?
                            :extra nil))
               ((erp inner? inner-span parstate) (read-token parstate))
               ((unless (and inner? (token-case inner? :ident)))
                (reterr-msg :where (span->start inner-span)
                            :expected "identifier in 'decltype'"
                            :found inner?
                            :extra nil))
               ((erp rp? rp-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rp? ")"))
                (reterr-msg :where (span->start rp-span)
                            :expected "')' after 'decltype' argument"
                            :found rp?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rp-span))))
            (retok (make-cpp-type-spec-decltype
                    :arg (make-cpp-expr-ident :name (token-ident->ident inner?)))
                   span parstate)))
         (base (make-cpp-type-spec-name :id id))
         ;; Check for '::' (qualified name)
         ((erp sep-token? & parstate) (read-token parstate))
         ((when (token-punctuatorp sep-token? "::"))
          ;; Qualified: parse the inner part recursively
          (b* (((erp inner inner-span parstate) (parse-cpp-type-spec-one parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end inner-span))))
            (retok (make-cpp-type-spec-qualified :scope id :inner inner)
                   span parstate)))
         ;; Put back the non-'::' token
         (parstate (if sep-token? (unread-token parstate) parstate))
         ;; Check for '<' (template instantiation)
         ((erp angle-token? & parstate) (read-token parstate))
         ((when (token-punctuatorp angle-token? "<"))
          ;; Template instantiation: parse args until '>'
          ;; Check for empty '<>'
          (b* (((erp empty-check? empty-span parstate) (read-token parstate))
               ((when (token-punctuatorp empty-check? ">"))
                ;; Empty template args: T<>
                (b* ((span (make-span :start (span->start tok-span)
                                      :end   (span->end empty-span))))
                  (retok (make-cpp-type-spec-template-inst :template base
                                                            :args nil)
                         span parstate)))
               ;; Not empty — put back and parse first arg
               (parstate (if empty-check? (unread-token parstate) parstate))
               (psize (parsize parstate))
               ((erp first-arg & parstate) (parse-cpp-type-spec-one parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ;; Parse remaining args (rank 0 < 1, parsize <=)
               ((erp args close-span parstate)
                (parse-cpp-type-spec-arg-list-rest (list first-arg) parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end close-span))))
            (retok (make-cpp-type-spec-template-inst :template base
                                                      :args args)
                   span parstate)))
         ;; No '<' — put back and return simple name
         (parstate (if angle-token? (unread-token parstate) parstate)))
      (retok base tok-span parstate)))

  ;; Recursive helper: parse comma-separated type specs for template args.
  ;; Starts AFTER the first type arg has been parsed (passed in `acc`).
  ;; Continues until '>' is consumed.
  (define parse-cpp-type-spec-arg-list-rest ((acc cpp-type-spec-listp)
                                              (parstate parstatep))
    :returns (mv erp
                 (args cpp-type-spec-listp)
                 (close-span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         ;; Peek: ',' or '>'
         ((erp sep-token? sep-span parstate) (read-token parstate))
         ;; '>' ends the argument list
         ((when (token-punctuatorp sep-token? ">"))
          (retok (cpp-type-spec-list-fix acc) sep-span parstate))
         ;; Must be ','
         ((unless (token-punctuatorp sep-token? ","))
          (reterr-msg :where (span->start sep-span)
                      :expected "',' or '>' in template argument list"
                      :found sep-token?
                      :extra nil))
         ;; Parse the next type arg (rank 1 > 0, but parsize decreased)
         (psize (parsize parstate))
         ((erp arg & parstate) (parse-cpp-type-spec-one parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Recurse
         ((erp result close-span parstate)
          (parse-cpp-type-spec-arg-list-rest (append (cpp-type-spec-list-fix acc)
                                                      (list arg))
                                              parstate)))
      (retok result close-span parstate)))

  ///

  (defthm-parse-cpp-type-spec-mutual-flag parsize-of-parse-cpp-type-spec-mutual-uncond
    (defthm parsize-of-parse-cpp-type-spec-one-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-type-spec-one parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-type-spec-one)
    (defthm parsize-of-parse-cpp-type-spec-arg-list-rest-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-type-spec-arg-list-rest acc parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-type-spec-arg-list-rest)
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-uncond
                                        c$::parsize-of-read-token-cond
                                        c$::parsize-of-unread-token)
             :expand ((parse-cpp-type-spec-one parstate)
                      (parse-cpp-type-spec-arg-list-rest acc parstate)))))

  (defthm-parse-cpp-type-spec-mutual-flag parsize-of-parse-cpp-type-spec-mutual-cond
    (defthm parsize-of-parse-cpp-type-spec-one-cond
      (implies (not (mv-nth 0 (parse-cpp-type-spec-one parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-type-spec-one parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-type-spec-one)
    (defthm parsize-of-parse-cpp-type-spec-arg-list-rest-cond
      (implies (not (mv-nth 0 (parse-cpp-type-spec-arg-list-rest acc parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-type-spec-arg-list-rest acc parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-type-spec-arg-list-rest)
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                        c$::parsize-of-read-token-uncond
                                        c$::parsize-of-unread-token)
             :expand ((parse-cpp-type-spec-one parstate)
                      (parse-cpp-type-spec-arg-list-rest acc parstate)))))

  (verify-guards parse-cpp-type-spec-one
    :hints (("Goal" :in-theory (enable c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Non-recursive entry point for parsing a type specifier.
(define parse-cpp-type-spec ((parstate parstatep))
  :returns (mv erp
               (spec cpp-type-spec-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ type specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a C++ type specifier: an optional @('const')/@('volatile') prefix,
     followed by an identifier (possibly qualified via @('::')
     or template-instantiated via @('< ... >')),
     followed by optional pointer (@('*')), lvalue reference (@('&')),
     or rvalue reference (@('&&')) suffixes.")
   (xdoc::p
    "Nested template arguments using @('>>') as two closing angles
     are a known limitation; the lexer produces @('>>') as a single
     token, so @('vector<vector<int>>') will not parse correctly."))
  (b* (((reterr) (irr-cpp-type-spec) (irr-span) parstate)
       ;; Parse the base type (no suffix)
       ((erp base base-span parstate) (parse-cpp-type-spec-one parstate))
       ;; Parse optional suffix
       ((erp result result-span parstate)
        (parse-cpp-type-spec-suffix base base-span parstate)))
    (retok result result-span parstate))

  ///

  (defret parsize-of-parse-cpp-type-spec-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-type-spec-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Typed Parameter
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-param ((parstate parstatep))
  :returns (mv erp
               (param cpp-param-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ typed function parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a type specifier followed by an optional parameter name.
     The name is taken if the next token is an identifier that is
     not @(',') or @(')') (which end the parameter).
     A leading @('[[attribute]]') is consumed and discarded if present;
     the parser recurses after discarding the attribute."))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-unread-token)))
  (b* (((reterr) (irr-cpp-param) (irr-span) parstate)
       ;; Peek at first token; check for '[' '[' (attribute specifier)
       ((erp peek1? & parstate) (read-token parstate))
       ((when (token-punctuatorp peek1? "["))
        ;; Read second token to see if we have [[
        (b* (((erp peek2? & parstate) (read-token parstate))
             ((unless (token-punctuatorp peek2? "["))
              ;; Not [[: put both tokens back and fall through to normal parsing
              (b* ((parstate (if peek2? (unread-token parstate) parstate))
                   (parstate (unread-token parstate))
                   ;; Parse the type
                   ((erp type-spec type-span parstate) (parse-cpp-type-spec parstate))
                   ;; Optional: parameter name
                   ((erp name-token? name-span parstate) (read-token parstate))
                   (name-p (and name-token?
                                (token-case name-token? :ident)
                                (not (token-punctuatorp name-token? ","))
                                (not (token-punctuatorp name-token? ")"))
                                (not (token-punctuatorp name-token? ">"))))
                   (param-name (if name-p (token-ident->ident name-token?) nil))
                   (end-span (if name-p name-span type-span))
                   (parstate (if (and name-token? (not name-p))
                                 (unread-token parstate)
                               parstate))
                   (span (make-span :start (span->start type-span)
                                    :end   (span->end end-span))))
                (retok (make-cpp-param :type type-spec :name param-name)
                       span parstate)))
             ;; Have [[: parse attribute name
             ((erp attr? attr-span parstate) (read-token parstate))
             ((unless (and attr? (token-case attr? :ident)))
              (reterr-msg :where (span->start attr-span)
                          :expected "attribute name inside [[ ]]"
                          :found attr?
                          :extra nil))
             ;; Optional ( arg )
             ((erp maybe-lp? & parstate) (read-token parstate))
             ((when (token-punctuatorp maybe-lp? "("))
              ;; Skip argument and closing paren, then fall through to ]]
              (b* (((erp & & parstate) (read-token parstate))  ; argument (discard)
                   ((erp rp? rp-span parstate) (read-token parstate))
                   ((unless (token-punctuatorp rp? ")"))
                    (reterr-msg :where (span->start rp-span)
                                :expected "')' to close attribute argument"
                                :found rp?
                                :extra nil))
                   ((erp rb1? rb1-span parstate) (read-token parstate))
                   ((unless (token-punctuatorp rb1? "]"))
                    (reterr-msg :where (span->start rb1-span)
                                :expected "']' in ']]'"
                                :found rb1?
                                :extra nil))
                   ((erp rb2? rb2-span parstate) (read-token parstate))
                   ((unless (token-punctuatorp rb2? "]"))
                    (reterr-msg :where (span->start rb2-span)
                                :expected "']]' to close attribute"
                                :found rb2?
                                :extra nil))
                   ;; Attribute consumed; recurse to parse the actual parameter
                   )
                (parse-cpp-param parstate)))
             ;; No '(': unread maybe-lp? and read ']]'
             (parstate (if maybe-lp? (unread-token parstate) parstate))
             ((erp rb1? rb1-span parstate) (read-token parstate))
             ((unless (token-punctuatorp rb1? "]"))
              (reterr-msg :where (span->start rb1-span)
                          :expected "']' in ']]'"
                          :found rb1?
                          :extra nil))
             ((erp rb2? rb2-span parstate) (read-token parstate))
             ((unless (token-punctuatorp rb2? "]"))
              (reterr-msg :where (span->start rb2-span)
                          :expected "']]' to close attribute"
                          :found rb2?
                          :extra nil)))
          ;; Attribute consumed; recurse to parse the actual parameter
          (parse-cpp-param parstate)))
       ;; No leading '[': put back and parse type normally
       (parstate (if peek1? (unread-token parstate) parstate))
       ;; Parse the type
       ((erp type-spec type-span parstate) (parse-cpp-type-spec parstate))
       ;; Optional: parameter name
       ((erp name-token? name-span parstate) (read-token parstate))
       (name-p (and name-token?
                    (token-case name-token? :ident)
                    (not (token-punctuatorp name-token? ","))
                    (not (token-punctuatorp name-token? ")"))
                    (not (token-punctuatorp name-token? ">"))))
       (param-name (if name-p (token-ident->ident name-token?) nil))
       (end-span (if name-p name-span type-span))
       (parstate (if (and name-token? (not name-p))
                     (unread-token parstate)
                   parstate))
       (span (make-span :start (span->start type-span)
                        :end   (span->end end-span))))
    (retok (make-cpp-param :type type-spec :name param-name)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-param-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param parstate)
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-uncond))))

  (defret parsize-of-parse-cpp-param-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param parstate)
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-cond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Parameter List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursive helper: parse remaining params after the first, separated by ','
(define parse-cpp-param-list-rest ((parstate parstatep))
  :returns (mv erp
               (params cpp-param-listp)
               (close-span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :parents nil
  (b* (((reterr) nil (irr-span) parstate)
       ;; Peek at the next token: ',' or ')'
       ((erp sep-token? sep-span parstate) (read-token parstate))
       ;; ')' ends the param list
       ((when (token-punctuatorp sep-token? ")"))
        (retok nil sep-span parstate))
       ;; Must be ','
       ((unless (token-punctuatorp sep-token? ","))
        (reterr-msg :where (span->start sep-span)
                    :expected "',' or ')' in parameter list"
                    :found sep-token?
                    :extra nil))
       ;; Parse next param
       ((erp param & parstate) (parse-cpp-param parstate))
       ;; Recurse
       ((erp rest close-span parstate) (parse-cpp-param-list-rest parstate)))
    (retok (cons param rest) close-span parstate))

  ///

  (defret parsize-of-parse-cpp-param-list-rest-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param-list-rest parstate)
             :in-theory (enable parsize-of-parse-cpp-param-cond))))

  (defret parsize-of-parse-cpp-param-list-rest-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param-list-rest parstate)
             :in-theory (enable parsize-of-parse-cpp-param-cond)))))

;; Non-recursive entry: parse params after '(' until ')'.
;; The caller has already consumed the '(' token.
(define parse-cpp-param-list ((parstate parstatep))
  :returns (mv erp
               (params cpp-param-listp)
               (close-span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ parameter list (contents between @('(') and @(')'))."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expects the @('(') to have been already consumed.
     Reads typed parameters separated by @(',') until @(')').
     Returns the parameter list and the span of the closing @(')')."))
  (b* (((reterr) nil (irr-span) parstate)
       ;; Check for empty parameter list: immediate ')'
       ((erp tok? tok-span parstate) (read-token parstate))
       ((when (token-punctuatorp tok? ")"))
        (retok nil tok-span parstate))
       ;; Not empty — put back and parse first param
       ((unless tok?)
        (reterr-msg :where (span->start tok-span)
                    :expected "')' or parameter in parameter list"
                    :found tok?
                    :extra nil))
       (parstate (unread-token parstate))
       ;; Parse first param
       ((erp first-param & parstate) (parse-cpp-param parstate))
       ;; Parse remaining params (or closing ')')
       ((erp rest-params close-span parstate)
        (parse-cpp-param-list-rest parstate)))
    (retok (cons first-param rest-params) close-span parstate))

  ///

  (defret parsize-of-parse-cpp-param-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-param-list-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Template Parameter and Template Parameter List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Mutual recursion: parse-cpp-template-param calls
;; parse-cpp-template-param-list-rest (for template template params),
;; and parse-cpp-template-param-list-rest calls parse-cpp-template-param.
;; Uses defines with two-nats-measure to handle this.

(defines parse-cpp-template-param-mutual
  :parents (parser)

  (define parse-cpp-template-param ((parstate parstatep))
    :returns (mv erp
                 (param cpp-template-param-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    :short "Parse a single C++ template parameter."
    :long
    (xdoc::topstring
     (xdoc::p
      "Parses a type parameter (@('typename T') or @('class T')),
       a non-type parameter (@('int N') or @('const T* ptr')),
       or a template template parameter
       (@('template<typename> class Container')).")
     (xdoc::p
      "Type parameters: the @('typename') or @('class') keyword is followed
       by an optional identifier (the parameter name).")
     (xdoc::p
      "Non-type parameters: parsed via @(tsee parse-cpp-type-spec) for the type,
       followed by a mandatory parameter name identifier.")
     (xdoc::p
      "Template template parameters: @('template') followed by @('< params >'),
       then @('typename') or @('class'), and an optional name."))
    (b* (((reterr) (irr-cpp-template-param) (irr-span) parstate)
         ((erp first-token? first-span parstate) (read-token parstate))
         ;; Template template parameter: starts with 'template'
         ((when (token-cpp-kw-p first-token? "template"))
          (b* (;; Read '<'
               ((erp open-token? open-span parstate) (read-token parstate))
               ((unless (token-punctuatorp open-token? "<"))
                (reterr-msg :where (span->start open-span)
                            :expected "'<' after 'template' in template template parameter"
                            :found open-token?
                            :extra nil))
               ;; Check for empty '<>'
               ((erp peek-token? peek-span parstate) (read-token parstate))
               ((when (token-punctuatorp peek-token? ">"))
                ;; Empty template params — read 'typename'/'class' + optional name
                (b* (((erp kw-token? & parstate) (read-token parstate))
                     ((unless (token-cpp-template-type-kw-p kw-token?))
                      (reterr-msg :where (span->start first-span)
                                  :expected "'typename' or 'class' after template<>"
                                  :found kw-token?
                                  :extra nil))
                     ((erp name-token? name-span parstate) (read-token parstate))
                     (name-p (and name-token?
                                  (token-case name-token? :ident)
                                  (not (token-punctuatorp name-token? ","))
                                  (not (token-punctuatorp name-token? ">"))))
                     (param-name (if name-p (token-ident->ident name-token?) nil))
                     (end-span (if name-p name-span peek-span))
                     (parstate (if (and name-token? (not name-p))
                                   (unread-token parstate)
                                 parstate))
                     (span (make-span :start (span->start first-span)
                                      :end   (span->end end-span))))
                  (retok (make-cpp-template-param-template-template
                          :params nil
                          :name   param-name)
                         span parstate)))
               ;; Not empty — put back and parse params
               (parstate (if peek-token? (unread-token parstate) parstate))
               (psize (parsize parstate))
               ((erp inner-params & parstate)
                (parse-cpp-template-param-list-rest open-span parstate))
               ((unless (mbt (<= (parsize parstate) psize)))
                (reterr :impossible))
               ;; Read 'typename' or 'class'
               ((erp kw-token? & parstate) (read-token parstate))
               ((unless (token-cpp-template-type-kw-p kw-token?))
                (reterr-msg :where (span->start first-span)
                            :expected "'typename' or 'class' after template<...>"
                            :found kw-token?
                            :extra nil))
               ;; Optional name
               ((erp name-token? name-span parstate) (read-token parstate))
               (name-p (and name-token?
                            (token-case name-token? :ident)
                            (not (token-punctuatorp name-token? ","))
                            (not (token-punctuatorp name-token? ">"))))
               (param-name (if name-p (token-ident->ident name-token?) nil))
               (end-span (if name-p name-span first-span))
               (parstate (if (and name-token? (not name-p))
                             (unread-token parstate)
                           parstate))
               (span (make-span :start (span->start first-span)
                                :end   (span->end end-span))))
            (retok (make-cpp-template-param-template-template
                    :params inner-params
                    :name   param-name)
                   span parstate)))
         ;; Type parameter introduced by 'typename' or 'class'
         ((when (token-cpp-template-type-kw-p first-token?))
          (b* ((typenamep (token-cpp-kw-p first-token? "typename"))
               ((erp name-token? name-span parstate) (read-token parstate))
               ((when (and name-token?
                           (token-case name-token? :ident)
                           (not (token-punctuatorp name-token? ","))
                           (not (token-punctuatorp name-token? ">"))))
                (b* ((name-ident (token-ident->ident name-token?))
                     (span (make-span :start (span->start first-span)
                                      :end   (span->end name-span))))
                  (retok (make-cpp-template-param-type
                          :typenamep typenamep
                          :name name-ident)
                         span parstate)))
               (parstate (if name-token? (unread-token parstate) parstate)))
            (retok (make-cpp-template-param-type :typenamep typenamep :name nil)
                   first-span parstate)))
         ;; Non-type parameter: parse type specifier + name
         ;; Put back the first token so parse-cpp-type-spec can read it
         ((unless (and first-token? (token-case first-token? :ident)))
          (reterr-msg :where (span->start first-span)
                      :expected "template parameter (typename/class T, type name N, or template<...>)"
                      :found first-token?
                      :extra nil))
         (parstate (unread-token parstate))
         ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
         ;; Parameter name (mandatory for non-type)
         ((erp name-token? name-span parstate) (read-token parstate))
         ((unless (and name-token? (token-case name-token? :ident)))
          (reterr-msg :where (span->start name-span)
                      :expected "parameter name after type in non-type template parameter"
                      :found name-token?
                      :extra nil))
         (param-ident (token-ident->ident name-token?))
         (span (make-span :start (span->start first-span)
                          :end   (span->end name-span))))
      (retok (make-cpp-template-param-nontype :type type-spec
                                              :param-name param-ident)
             span parstate)))

  (define parse-cpp-template-param-list-rest ((open-span spanp)
                                               (parstate parstatep))
    :returns (mv erp
                 (params cpp-template-param-listp)
                 (close-span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :measure (two-nats-measure (parsize parstate) 1)
    :verify-guards nil
    :parents nil
    (b* (((reterr) nil (irr-span) parstate)
         ;; Parse one parameter
         (psize (parsize parstate))
         ((erp param & parstate) (parse-cpp-template-param parstate))
         ((unless (mbt (<= (parsize parstate) psize)))
          (reterr :impossible))
         ;; Peek at the next token: ',' or '>'
         ((erp sep-token? sep-span parstate) (read-token parstate))
         ;; End of list
         ((when (token-punctuatorp sep-token? ">"))
          (retok (list param) sep-span parstate))
         ;; More parameters after ','
         ((unless (token-punctuatorp sep-token? ","))
          (reterr-msg :where (span->start sep-span)
                      :expected "',' or '>' in template parameter list"
                      :found sep-token?
                      :extra nil))
         ;; Recurse
         ((erp rest-params close-span parstate)
          (parse-cpp-template-param-list-rest open-span parstate)))
      (retok (cons param rest-params) close-span parstate)))

  ///

  (defthm-parse-cpp-template-param-mutual-flag parsize-of-parse-cpp-template-param-mutual-uncond
    (defthm parsize-of-parse-cpp-template-param-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-template-param parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-template-param)
    (defthm parsize-of-parse-cpp-template-param-list-rest-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-template-param-list-rest open-span parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-template-param-list-rest)
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token
                                       parse-cpp-template-param
                                       parse-cpp-template-param-list-rest))))

  (defthm-parse-cpp-template-param-mutual-flag parsize-of-parse-cpp-template-param-mutual-cond
    (defthm parsize-of-parse-cpp-template-param-cond
      (implies (not (mv-nth 0 (parse-cpp-template-param parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-template-param parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-template-param)
    (defthm parsize-of-parse-cpp-template-param-list-rest-cond
      (implies (not (mv-nth 0 (parse-cpp-template-param-list-rest open-span parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-template-param-list-rest open-span parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-template-param-list-rest)
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token
                                       parse-cpp-template-param
                                       parse-cpp-template-param-list-rest))))

  (verify-guards parse-cpp-template-param
    :hints (("Goal" :in-theory (enable c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Template Parameter List (non-recursive entry point)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-template-param-list ((parstate parstatep))
  :returns (mv erp
               (params cpp-template-param-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ template parameter list: @('< param1 , param2 , ... >')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the entire @('< ... >') delimited template parameter list.
     Expects the leading @('<') token to be the next token in the stream.
     Reads parameters separated by @(',') until the closing @('>')."))
  (b* (((reterr) nil (irr-span) parstate)
       ;; Read opening '<'
       ((erp open-token? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open-token? "<"))
        (reterr-msg :where (span->start open-span)
                    :expected "'<' to begin template parameter list"
                    :found open-token?
                    :extra nil))
       ;; Check for empty parameter list '<>'
       ((erp peek-token? peek-span parstate) (read-token parstate))
       ((when (token-punctuatorp peek-token? ">"))
        (retok nil (make-span :start (span->start open-span)
                              :end   (span->end peek-span))
               parstate))
       ;; Not empty — put back the peek token and parse parameters
       (parstate (if peek-token? (unread-token parstate) parstate))
       ;; Parse the comma-separated list of parameters
       ((erp params close-span parstate)
        (parse-cpp-template-param-list-rest open-span parstate)))
    (retok params
           (make-span :start (span->start open-span)
                      :end   (span->end close-span))
           parstate))

  ///

  (defret parsize-of-parse-cpp-template-param-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-template-param-list-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Namespace Definition Header
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-namespace-def-header ((parstate parstatep))
  :returns (mv erp
               (ns-def cpp-namespace-def-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ namespace definition header: @('namespace [Name]')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the @('namespace') keyword and the optional name (or name sequence
     for nested namespaces using @('::') as the separator).
     Does NOT parse the @('{') @('...') @('}') body.")
   (xdoc::p
    "Returns a @(tsee cpp-namespace-def) value describing the kind of namespace:
     anonymous, named, or nested."))
  (b* (((reterr) (irr-cpp-namespace-def) (irr-span) parstate)
       ;; Read the 'namespace' keyword (arrives as identifier)
       ((erp ns-token? ns-span parstate) (read-token parstate))
       ((unless (token-cpp-kw-p ns-token? "namespace"))
        (reterr-msg :where (span->start ns-span)
                    :expected "'namespace' keyword"
                    :found ns-token?
                    :extra nil))
       ;; Check if this is an anonymous namespace (next token is '{')
       ((erp next-token? next-span parstate) (read-token parstate))
       ((when (token-punctuatorp next-token? "{"))
        ;; Anonymous namespace: put back the '{'
        (b* ((parstate (unread-token parstate)))
          (retok (make-cpp-namespace-def
                  :kind    (cpp-namespace-kind-anonymous)
                  :inlinep nil
                  :body    nil)
                 ns-span parstate)))
       ;; Must be a name identifier
       ((unless (and next-token? (token-case next-token? :ident)))
        (reterr-msg :where (span->start next-span)
                    :expected "namespace name or '{' after 'namespace'"
                    :found next-token?
                    :extra nil))
       (first-name (token-ident->ident next-token?))
       ;; Check for nested namespace using '::'
       ((erp sep-token? & parstate) (read-token parstate))
       ((when (token-punctuatorp sep-token? "::"))
        ;; Nested namespace: collect remaining names
        (b* (((erp rest-names last-span parstate)
              (parse-cpp-nested-namespace-names parstate))
             (span (make-span :start (span->start ns-span)
                              :end   (span->end last-span))))
          (retok (make-cpp-namespace-def
                  :kind    (make-cpp-namespace-kind-nested
                            :names (cons first-name rest-names))
                  :inlinep nil
                  :body    nil)
                 span parstate)))
       ;; Single named namespace — put back sep-token?
       (parstate (if sep-token? (unread-token parstate) parstate))
       (span (make-span :start (span->start ns-span)
                        :end   (span->end next-span))))
    (retok (make-cpp-namespace-def
            :kind    (make-cpp-namespace-kind-named :name first-name)
            :inlinep nil
            :body    nil)
           span parstate))

  :prepwork
  ((define parse-cpp-nested-namespace-names ((parstate parstatep))
     :returns (mv erp
                  (names ident-listp)
                  (last-span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :measure (parsize parstate)
     :parents nil
     :short "Parse the tail of a nested namespace name: @('A::B::C') after the first name."
     (b* (((reterr) nil (irr-span) parstate)
          ;; Read the next name identifier
          ((erp name-token? name-span parstate) (read-token parstate))
          ((unless (and name-token? (token-case name-token? :ident)))
           (reterr-msg :where (span->start name-span)
                       :expected "namespace name identifier after '::'"
                       :found name-token?
                       :extra nil))
          (name (token-ident->ident name-token?))
          ;; Check for another '::'
          ((erp sep-token? & parstate) (read-token parstate))
          ((when (token-punctuatorp sep-token? "::"))
           ;; More segments
           (b* (((erp rest-names last-span parstate)
                 (parse-cpp-nested-namespace-names parstate)))
             (retok (cons name rest-names) last-span parstate)))
          ;; End of the nested name — put back whatever we peeked
          (parstate (if sep-token? (unread-token parstate) parstate)))
       (retok (list name) name-span parstate))

     ///

     (defret parsize-of-parse-cpp-nested-namespace-names-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable c$::parsize-of-read-token-cond
                                   c$::parsize-of-unread-token))))

     (defret parsize-of-parse-cpp-nested-namespace-names-cond
       (implies (not erp)
                (< (parsize new-parstate)
                   (parsize parstate)))
       :rule-classes :linear
       :hints (("Goal"
                :induct t
                :in-theory (enable c$::parsize-of-read-token-cond
                                   c$::parsize-of-unread-token))))))

  ///

  (defret parsize-of-parse-cpp-namespace-def-header-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Base Specifier
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: parse one base specifier: [access-spec] class-type-spec
(define parse-cpp-base-specifier ((parstate parstatep))
  :returns (mv erp
               (spec cpp-base-specifier-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ base class specifier: @('[access] type-spec')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses an optional access specifier (@('public'), @('private'),
     or @('protected')) followed by the base class type specifier.
     If no access specifier is present, defaults to @('public')."))
  (b* (((reterr) (irr-cpp-base-specifier) (irr-span) parstate)
       ;; Read the first token — may be an access specifier or start of type
       ((erp first-token? first-span parstate) (read-token parstate))
       ;; Check if the first token is an access specifier
       ((when (token-cpp-access-spec-p first-token?))
        (b* ((access (token-to-cpp-access-spec first-token?))
             ;; Parse the class type specifier
             ((erp class-type class-span parstate)
              (parse-cpp-type-spec parstate))
             (span (make-span :start (span->start first-span)
                              :end   (span->end class-span))))
          (retok (make-cpp-base-specifier :access access
                                          :class-name class-type)
                 span parstate)))
       ;; No access specifier — first token starts the class type
       ;; Put it back and parse the type specifier
       ((unless first-token?)
        (reterr-msg :where (span->start first-span)
                    :expected "access specifier or class name in base specifier"
                    :found first-token?
                    :extra nil))
       (parstate (unread-token parstate))
       ((erp class-type class-span parstate) (parse-cpp-type-spec parstate)))
    ;; Default access: public
    (retok (make-cpp-base-specifier :access (cpp-access-spec-public)
                                    :class-name class-type)
           class-span parstate))

  ///

  (defret parsize-of-parse-cpp-base-specifier-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-base-specifier-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Base Clause
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Forward declare the rest helper inside parse-cpp-base-clause's prepwork.
(define parse-cpp-base-clause ((parstate parstatep))
  :returns (mv erp
               (bases cpp-base-specifier-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ base clause: @(': base-spec { , base-spec }*')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the @(':') delimiter and then one or more base specifiers
     separated by @(',').
     Returns the list of base specifiers and the overall span."))
  (b* (((reterr) nil (irr-span) parstate)
       ;; Read the ':' delimiter
       ((erp colon-token? colon-span parstate) (read-token parstate))
       ((unless (token-punctuatorp colon-token? ":"))
        (reterr-msg :where (span->start colon-span)
                    :expected "':' to begin base clause"
                    :found colon-token?
                    :extra nil))
       ;; Parse the first base specifier
       ((erp first-spec first-spec-span parstate)
        (parse-cpp-base-specifier parstate))
       ;; Check for more base specifiers separated by ','
       ((erp sep-token? & parstate) (read-token parstate))
       ((when (not (token-punctuatorp sep-token? ",")))
        ;; No more — put the token back
        (b* ((parstate (if sep-token? (unread-token parstate) parstate))
             (span (make-span :start (span->start colon-span)
                              :end   (span->end first-spec-span))))
          (retok (list first-spec) span parstate)))
       ;; There are more; delegate to the recursive helper
       ((erp rest-specs last-span parstate)
        (parse-cpp-base-clause-rest parstate))
       (span (make-span :start (span->start colon-span)
                        :end   (span->end last-span))))
    (retok (cons first-spec rest-specs) span parstate))

  :prepwork
  ((define parse-cpp-base-clause-rest ((parstate parstatep))
     :returns (mv erp
                  (specs cpp-base-specifier-listp)
                  (last-span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :measure (parsize parstate)
     :parents nil
     :short "Parse the tail of a base clause after the first @(',')."
     (b* (((reterr) nil (irr-span) parstate)
          ;; Parse one base specifier
          ((erp spec spec-span parstate) (parse-cpp-base-specifier parstate))
          ;; Check for ','
          ((erp sep-token? & parstate) (read-token parstate))
          ((when (not (token-punctuatorp sep-token? ",")))
           ;; Done — put separator back
           (b* ((parstate (if sep-token? (unread-token parstate) parstate)))
             (retok (list spec) spec-span parstate)))
          ;; Recurse
          ((erp rest last-span parstate)
           (parse-cpp-base-clause-rest parstate)))
       (retok (cons spec rest) last-span parstate))

     ///

     (defret parsize-of-parse-cpp-base-clause-rest-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal"
                :induct (parse-cpp-base-clause-rest parstate)
                :in-theory (enable parsize-of-parse-cpp-base-specifier-cond
                                   c$::parsize-of-unread-token))))

     (defret parsize-of-parse-cpp-base-clause-rest-cond
       (implies (not erp)
                (< (parsize new-parstate)
                   (parsize parstate)))
       :rule-classes :linear
       :hints (("Goal"
                :induct (parse-cpp-base-clause-rest parstate)
                :in-theory (enable parsize-of-parse-cpp-base-specifier-cond
                                   c$::parsize-of-unread-token))))))

  ///

  (defret parsize-of-parse-cpp-base-clause-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Enumerator and Enum Declaration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-enumerator ((parstate parstatep))
  :returns (mv erp
               (enumerator cpp-enumerator-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ enumerator: @('name [= const-expr]')."
  (b* (((reterr) (irr-cpp-enumerator) (irr-span) parstate)
       ;; Enumerator name
       ((erp name-tok? name-span parstate) (read-token parstate))
       ((unless (and name-tok? (token-case name-tok? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "enumerator name"
                    :found name-tok?
                    :extra nil))
       (name (token-ident->ident name-tok?))
       ;; Optional '= value'
       ((erp eq-tok? & parstate) (read-token parstate))
       ((when (not (token-punctuatorp eq-tok? "=")))
        ;; No value — put back eq-tok? if non-nil
        (b* ((parstate (if eq-tok? (unread-token parstate) parstate)))
          (retok (make-cpp-enumerator
                  :name    name
                  :value-p nil
                  :value   (irr-cpp-const-expr))
                 name-span parstate)))
       ;; Value: 'true', 'false', identifier, or integer constant
       ((erp val-tok? val-span parstate) (read-token parstate))
       ((mv const-val ok)
        (cond ((token-cpp-kw-p val-tok? "true")
               (mv (make-cpp-const-expr-bool :value t) t))
              ((token-cpp-kw-p val-tok? "false")
               (mv (make-cpp-const-expr-bool :value nil) t))
              ((and val-tok? (token-case val-tok? :ident))
               (mv (make-cpp-const-expr-ident
                    :name (token-ident->ident val-tok?)) t))
              ((and val-tok? (token-case val-tok? :const)
                   (c$::const-case (c$::token-const->const val-tok?) :int))
               (mv (make-cpp-const-expr-int
                    :iconst (c$::const-int->iconst
                             (c$::token-const->const val-tok?))) t))
              (t (mv (irr-cpp-const-expr) nil))))
       ((unless ok)
        (reterr-msg :where (span->start val-span)
                    :expected "constant value in enumerator"
                    :found val-tok?
                    :extra nil))
       (span (make-span :start (span->start name-span)
                        :end   (span->end val-span))))
    (retok (make-cpp-enumerator
            :name    name
            :value-p t
            :value   const-val)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-enumerator-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-enumerator-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

(define parse-cpp-enumerator-list-rest ((parstate parstatep))
  :returns (mv erp
               (enumerators cpp-enumerator-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse the tail of a C++ enumerator list: @('{, enumerator}*')."
  :measure (parsize parstate)
  (b* (((reterr) nil (irr-span) parstate)
       ;; Peek: ',' means more enumerators; '}' or EOF means done
       ((erp peek? & parstate) (read-token parstate))
       ((when (not (token-punctuatorp peek? ",")))
        ;; Not a comma — put back and return empty
        (b* ((parstate (if peek? (unread-token parstate) parstate)))
          (retok nil (irr-span) parstate)))
       ;; Consumed ','.  Now peek again: '}' means trailing comma — done
       ((erp peek2? peek2-span parstate) (read-token parstate))
       ((when (or (not peek2?)
                  (token-punctuatorp peek2? "}")))
        ;; Trailing comma (or unexpected EOF) — put back and return
        (b* ((parstate (if peek2? (unread-token parstate) parstate)))
          (retok nil peek2-span parstate)))
       (parstate (unread-token parstate))
       ;; Parse next enumerator
       ((erp enum enum-span parstate) (parse-cpp-enumerator parstate))
       ;; Recurse
       ((erp rest & parstate) (parse-cpp-enumerator-list-rest parstate)))
    (retok (cons enum rest) enum-span parstate))

  ///

  (defret parsize-of-parse-cpp-enumerator-list-rest-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-enumerator-list-rest parstate)
             :in-theory (enable c$::parsize-of-read-token-uncond
                                c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-enumerator-uncond)))))

(define parse-cpp-enum-decl ((parstate parstatep))
  :returns (mv erp
               (decl cpp-enum-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ enum declaration: @('enum [class|struct] [name] [: base] { ... }')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads the @('enum') keyword.
     Checks for @('class') or @('struct') (making it a scoped enum).
     Reads an optional name identifier.
     Checks for @(':') followed by a base type specifier.
     Reads @('{'), the enumerator list, and @('}').
     Returns a @(tsee cpp-enum-decl)."))
  (b* (((reterr) (irr-cpp-enum-decl) (irr-span) parstate)
       ;; Read 'enum'
       ((erp enum-tok? enum-span parstate) (read-token parstate))
       ((unless (token-keywordp enum-tok? "enum"))
        (reterr-msg :where (span->start enum-span)
                    :expected "'enum' keyword"
                    :found enum-tok?
                    :extra nil))
       ;; Optional 'class' or 'struct'
       ((erp cls-tok? & parstate) (read-token parstate))
       (classp (or (token-cpp-kw-p cls-tok? "class")
                   (token-keywordp cls-tok? "struct")))
       (parstate (if (and cls-tok? (not classp))
                     (unread-token parstate)
                   parstate))
       ;; Optional name
       ((erp name-tok? & parstate) (read-token parstate))
       ((mv name parstate)
        (if (and name-tok? (token-case name-tok? :ident))
            (mv (token-ident->ident name-tok?) parstate)
          (let* ((parstate (if name-tok? (unread-token parstate) parstate)))
            (mv nil parstate))))
       ;; Optional ': base-type'
       ((erp colon-tok? & parstate) (read-token parstate))
       (has-base (token-punctuatorp colon-tok? ":"))
       (parstate (if (and colon-tok? (not has-base))
                     (unread-token parstate)
                   parstate))
       ((erp base-type & parstate)
        (if has-base
            (parse-cpp-type-spec parstate)
          (mv nil (irr-cpp-type-spec) (irr-span) parstate)))
       ;; Read '{'
       ((erp lbrace? lbrace-span parstate) (read-token parstate))
       ((unless (token-punctuatorp lbrace? "{"))
        (reterr-msg :where (span->start lbrace-span)
                    :expected "'{' to open enum body"
                    :found lbrace?
                    :extra nil))
       ;; Parse first enumerator (if not '}' immediately)
       ((erp peek? peek-span parstate) (read-token parstate))
       ;; Put peek? back (or leave parstate at EOF as-is)
       (parstate (if peek? (unread-token parstate) parstate))
       ;; Determine if body is empty
       (empty-body? (or (not peek?) (token-punctuatorp peek? "}")))
       ;; Parse first enumerator (if body non-empty)
       ((erp first-enum & parstate)
        (if empty-body?
            (mv nil (irr-cpp-enumerator) peek-span parstate)
          (parse-cpp-enumerator parstate)))
       ;; Parse remaining enumerators (if body non-empty)
       ((erp rest-enums & parstate)
        (if empty-body?
            (mv nil nil (irr-span) parstate)
          (parse-cpp-enumerator-list-rest parstate)))
       ;; Build enum body
       (enum-body (if empty-body? nil (cons first-enum rest-enums)))
       ;; Read '}'
       ((erp rbrace? rbrace-span parstate) (read-token parstate))
       ((unless (token-punctuatorp rbrace? "}"))
        (reterr-msg :where (span->start rbrace-span)
                    :expected "'}' to close enum body"
                    :found rbrace?
                    :extra nil))
       ;; Read ';'
       ((erp semi? semi-span parstate) (read-token parstate))
       ((unless (token-punctuatorp semi? ";"))
        (reterr-msg :where (span->start semi-span)
                    :expected "';' after enum declaration"
                    :found semi?
                    :extra nil))
       (span (make-span :start (span->start enum-span)
                        :end   (span->end semi-span))))
    (retok (make-cpp-enum-decl
            :classp  classp
            :name    name
            :base-p  has-base
            :base    (if has-base base-type (irr-cpp-type-spec))
            :body    enum-body)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-enum-decl-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-enum-decl-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-cond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Using Declaration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-using-decl ((parstate parstatep))
  :returns (mv erp
               (decl cpp-using-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ using declaration: @('using Name = Type;') or @('using ns::Foo;')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads the @('using') keyword.
     Peeks ahead: if the next two tokens are @('ident ='), it is an alias
     (@(':alias') variant); otherwise it is a name import parsed as a
     type specifier (@(':name') variant).
     Both forms are terminated by @(';')."))
  (b* (((reterr) (irr-cpp-using-decl) (irr-span) parstate)
       ;; Read 'using'
       ((erp using-tok? using-span parstate) (read-token parstate))
       ((unless (token-cpp-kw-p using-tok? "using"))
        (reterr-msg :where (span->start using-span)
                    :expected "'using' keyword"
                    :found using-tok?
                    :extra nil))
       ;; Peek at next token — ident followed by '=' means alias form
       ((erp first-tok? & parstate) (read-token parstate))
       ((erp second-tok? & parstate) (read-token parstate))
       ((mv is-alias parstate)
        (if (and (and first-tok? (token-case first-tok? :ident))
                 (token-punctuatorp second-tok? "="))
            ;; Alias form: keep first-tok? consumed; second-tok? ('=') consumed
            (mv t parstate)
          ;; Not alias: put both tokens back
          (b* ((parstate (if second-tok? (unread-token parstate) parstate))
               (parstate (if first-tok?  (unread-token parstate) parstate)))
            (mv nil parstate))))
       ;; --- Alias form: 'using Alias = Type ;' ---
       ((when is-alias)
        (b* ((alias (token-ident->ident first-tok?))
             ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
             ((erp semi? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after using-alias declaration"
                          :found semi?
                          :extra nil))
             (span (make-span :start (span->start using-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-using-decl-alias :alias alias :type type-spec)
                 span parstate)))
       ;; --- Name form: 'using ns::Foo ;' ---
       ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
       ((erp semi? semi-span parstate) (read-token parstate))
       ((unless (token-punctuatorp semi? ";"))
        (reterr-msg :where (span->start semi-span)
                    :expected "';' after using declaration"
                    :found semi?
                    :extra nil))
       (span (make-span :start (span->start using-span)
                        :end   (span->end semi-span))))
    (retok (make-cpp-using-decl-name :name type-spec) span parstate))

  ///

  (defret parsize-of-parse-cpp-using-decl-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-using-decl-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-type-spec-cond)))))



(define parse-cpp-member-access-label ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ member access label: @('public:'), @('private:'), or @('protected:')."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ;; Read the access specifier
       ((erp access-token? access-span parstate) (read-token parstate))
       ((unless (token-cpp-access-spec-p access-token?))
        (reterr-msg :where (span->start access-span)
                    :expected "access specifier for member access label"
                    :found access-token?
                    :extra nil))
       (spec (token-to-cpp-access-spec access-token?))
       ;; Read the ':'
       ((erp colon-token? colon-span parstate) (read-token parstate))
       ((unless (token-punctuatorp colon-token? ":"))
        (reterr-msg :where (span->start colon-span)
                    :expected "':' after access specifier"
                    :found colon-token?
                    :extra nil))
       (span (make-span :start (span->start access-span)
                        :end   (span->end colon-span))))
    (retok (make-cpp-member-decl-access :spec spec) span parstate))

  ///

  (defret parsize-of-parse-cpp-member-access-label-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-member-access-label-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Noexcept Specifier
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-noexcept-spec ((parstate parstatep))
  :returns (mv erp
               (spec cpp-noexcept-spec-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ @('noexcept') specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads the @('noexcept') keyword.
     If the next token is @('('), reads a constant expression and @(')'),
     returning an @(':expr') noexcept spec.
     Otherwise, returns a @(':bare') noexcept spec.")
   (xdoc::p
    "Inside the parentheses, @('true')/@('false') produce a
     @(tsee cpp-const-expr-bool), and an identifier produces a
     @(tsee cpp-const-expr-ident)."))
  (b* (((reterr) (irr-cpp-noexcept-spec) (irr-span) parstate)
       ;; Read 'noexcept'
       ((erp noex-token? noex-span parstate) (read-token parstate))
       ((unless (token-cpp-noexcept-p noex-token?))
        (reterr-msg :where (span->start noex-span)
                    :expected "'noexcept' keyword"
                    :found noex-token?
                    :extra nil))
       ;; Peek for '('
       ((erp paren-token? & parstate) (read-token parstate))
       ((when (not (token-punctuatorp paren-token? "(")))
        ;; Bare 'noexcept'
        (b* ((parstate (if paren-token? (unread-token parstate) parstate)))
          (retok (cpp-noexcept-spec-bare) noex-span parstate)))
       ;; Read the expression token: 'true', 'false', or an identifier
       ((erp expr-token? expr-span parstate) (read-token parstate))
       ((mv const-expr ok)
        (cond ((token-cpp-kw-p expr-token? "true")
               (mv (make-cpp-const-expr-bool :value t) t))
              ((token-cpp-kw-p expr-token? "false")
               (mv (make-cpp-const-expr-bool :value nil) t))
              ((and expr-token? (token-case expr-token? :ident))
               (mv (make-cpp-const-expr-ident
                    :name (token-ident->ident expr-token?)) t))
              (t (mv (irr-cpp-const-expr) nil))))
       ((unless ok)
        (reterr-msg :where (span->start expr-span)
                    :expected "'true', 'false', or identifier in noexcept()"
                    :found expr-token?
                    :extra nil))
       ;; Read ')'
       ((erp close-token? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close-token? ")"))
        (reterr-msg :where (span->start close-span)
                    :expected "')' after noexcept(expr)"
                    :found close-token?
                    :extra nil))
       (span (make-span :start (span->start noex-span)
                        :end   (span->end close-span))))
    (retok (make-cpp-noexcept-spec-expr :value const-expr) span parstate))

  ///

  (defret parsize-of-parse-cpp-noexcept-spec-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-noexcept-spec-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Field or Method
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-field-or-method ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ member field or method declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a member declaration of the form:
     @('[virtual] [static|mutable] type-spec name [( params )] [const] [noexcept[(expr)]] [= 0] ;').")
   (xdoc::p
    "Strategy: read optional qualifiers (@('virtual'), @('static'), @('mutable')),
     then the type specifier via @(tsee parse-cpp-type-spec),
     then the member name identifier.
     Peek at the next token: if @('('), it is a method; otherwise it is a field.
     For methods, parse typed parameters via @(tsee parse-cpp-param-list),
     then check for @('const'), @('noexcept'), and @('= 0') before the @(';')."))
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ;; Read first token — may be a qualifier or type
       ((erp t1? t1-span parstate) (read-token parstate))
       ;; --- Detect 'virtual' ---
       (virtualp (token-cpp-kw-p t1? "virtual"))
       ((erp t1? t1-span parstate)
        (if virtualp
            (read-token parstate)
          (mv nil t1? t1-span parstate)))
       ;; --- Detect 'static' or 'mutable' ---
       (staticp (token-keywordp t1? "static"))
       (mutablep (and (not staticp) (token-cpp-kw-p t1? "mutable")))
       ;; If we found static/mutable, we need to put back t1? and parse type spec
       ;; Otherwise t1? is the start of the type
       ((erp t1? t1-span parstate)
        (if (or staticp mutablep)
            (read-token parstate)
          (mv nil t1? t1-span parstate)))
       ;; --- Type specifier ---
       ;; Put back the token so parse-cpp-type-spec can read it
       ((unless (and t1? (or (token-case t1? :ident) (token-case t1? :keyword))))
        (reterr-msg :where (span->start t1-span)
                    :expected "type specifier in member declaration"
                    :found t1?
                    :extra nil))
       (parstate (unread-token parstate))
       ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
       ;; --- Member name ---
       ((erp name-token? name-span parstate) (read-token parstate))
       ((unless (and name-token? (token-case name-token? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "member name identifier"
                    :found name-token?
                    :extra nil))
       (name-ident (token-ident->ident name-token?))
       ;; --- Peek: '(' means method, otherwise field ---
       ((erp peek-token? & parstate) (read-token parstate))
       ;; --- FIELD case ---
       ((when (not (token-punctuatorp peek-token? "(")))
        ;; Put back peek and expect ';'
        (b* ((parstate (if peek-token? (unread-token parstate) parstate))
             ((erp semi-token? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi-token? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after field declaration"
                          :found semi-token?
                          :extra nil))
             (span (make-span :start (span->start t1-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-field
                  :type-name  type-spec
                  :field-name name-ident
                  :staticp    staticp
                  :mutablep   mutablep
                  :constexprp nil)
                 span parstate)))
       ;; --- METHOD case: peek-token? = '(' ---
       ;; Parse typed parameter list
       ((erp params & parstate) (parse-cpp-param-list parstate))
       ;; Check for 'const'
       ((erp const-token? & parstate) (read-token parstate))
       (const-qualp (token-keywordp const-token? "const"))
       (parstate (if (and const-token? (not const-qualp))
                     (unread-token parstate)
                   parstate))
       ;; Check for 'noexcept' — if present, parse full noexcept spec
       ((erp noexcept-token? & parstate) (read-token parstate))
       (noexcept-p (token-cpp-noexcept-p noexcept-token?))
       (parstate (if noexcept-token? (unread-token parstate) parstate))
       ((erp noexcept-raw & parstate)
        (if noexcept-p
            (parse-cpp-noexcept-spec parstate)
          (mv nil (irr-cpp-noexcept-spec) (irr-span) parstate)))
       (noexcept-spec (if noexcept-p
                          (cpp-noexcept-spec-option-some noexcept-raw)
                        nil))
       ;; Check for '= 0' (pure virtual): read '=' first
       ((erp eq-token? & parstate) (read-token parstate))
       ;; If we got '=', read the next token to check for integer '0'
       ((erp zero-token? & parstate)
        (if (token-punctuatorp eq-token? "=")
            (read-token parstate)
          (mv nil nil (irr-span) parstate)))
       ;; Determine pure-virtualp
       (pure-virtualp (and (token-punctuatorp eq-token? "=")
                           (and zero-token? (token-case zero-token? :const))))
       ;; Put back tokens if not '= 0'
       (parstate
        (cond
         (pure-virtualp parstate)
         ((token-punctuatorp eq-token? "=")
          ;; Had '=' but zero-token? was not a constant: put both back
          (let* ((parstate (if zero-token? (unread-token parstate) parstate))
                 (parstate (unread-token parstate)))
            parstate))
         (t
          ;; eq-token? was not '=': put it back if non-nil
          (if eq-token? (unread-token parstate) parstate))))
       ;; Expect ';'
       ((erp semi-token? semi-span parstate) (read-token parstate))
       ((unless (token-punctuatorp semi-token? ";"))
        (reterr-msg :where (span->start semi-span)
                    :expected "';' after method declaration"
                    :found semi-token?
                    :extra nil))
       (span (make-span :start (span->start t1-span)
                        :end   (span->end semi-span))))
    (retok (make-cpp-member-decl-method
            :return-type   type-spec
            :method-id     (make-cpp-member-name-simple :id name-ident)
            :params        params
            :virtualp      virtualp
            :const-qualp   const-qualp
            :noexcept-spec noexcept-spec
            :pure-virtualp pure-virtualp
            :staticp       staticp
            :body-p        nil
            :body          nil
            :destructorp   nil
            :explicitp     nil
            :constexprp    nil
            :inlinep       nil
            :ctor-init-p   nil
            :ctor-init-list nil)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-member-field-or-method-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-uncond
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-type-spec-uncond
                                       parsize-of-parse-cpp-param-list-uncond
                                       parsize-of-parse-cpp-noexcept-spec-uncond)
             :expand ((parse-cpp-member-field-or-method parstate)))))

  (defret parsize-of-parse-cpp-member-field-or-method-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-read-token-uncond
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-type-spec-cond
                                       parsize-of-parse-cpp-param-list-cond
                                       parsize-of-parse-cpp-noexcept-spec-cond)
             :expand ((parse-cpp-member-field-or-method parstate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Declaration Item
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-decl-item ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ class member declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Dispatches to either @(tsee parse-cpp-member-access-label)
     (for @('public:') / @('private:') / @('protected:'))
     or @(tsee parse-cpp-member-field-or-method)
     (for field and method declarations).
     The dispatch peeks at the first token to decide which case applies."))
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ;; Peek at the first token
       ((erp peek-token? peek-span parstate) (read-token parstate))
       ;; Access label: 'public', 'private', or 'protected'
       ((when (token-cpp-access-spec-p peek-token?))
        ;; Put it back; parse-cpp-member-access-label will re-read it
        (b* ((parstate (unread-token parstate)))
          (parse-cpp-member-access-label parstate)))
       ;; Using declaration: 'using ...'
       ((when (token-cpp-kw-p peek-token? "using"))
        (b* ((parstate (unread-token parstate))
             ((erp decl span parstate) (parse-cpp-using-decl parstate)))
          (retok (make-cpp-member-decl-using-decl :decl decl) span parstate)))
       ;; Enum declaration: 'enum ...'
       ((when (token-keywordp peek-token? "enum"))
        (b* ((parstate (unread-token parstate))
             ((erp def span parstate) (parse-cpp-enum-decl parstate)))
          (retok (make-cpp-member-decl-enum-decl :def def) span parstate)))
       ;; Friend declaration: 'friend' 'class'/'struct' type-spec ';'
       ((when (token-cpp-kw-p peek-token? "friend"))
        ;; peek-token? ('friend') is already consumed
        (b* (((erp cls? cls-span parstate) (read-token parstate))
             ((unless (or (token-cpp-kw-p cls? "class")
                          (token-keywordp cls? "struct")))
              (reterr-msg :where (span->start cls-span)
                          :expected "'class' or 'struct' after 'friend'"
                          :found cls?
                          :extra nil))
             ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
             ((erp semi? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after friend declaration"
                          :found semi?
                          :extra nil))
             (span (make-span :start (span->start peek-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-friend :subject type-spec) span parstate)))
       ;; Typedef: 'typedef' type-spec name ';'
       ((when (token-keywordp peek-token? "typedef"))
        ;; peek-token? ('typedef') is already consumed
        (b* (((erp type-spec & parstate) (parse-cpp-type-spec parstate))
             ((erp name? name-span parstate) (read-token parstate))
             ((unless (and name? (token-case name? :ident)))
              (reterr-msg :where (span->start name-span)
                          :expected "type alias name after 'typedef'"
                          :found name?
                          :extra nil))
             ((erp semi? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after typedef"
                          :found semi?
                          :extra nil))
             (span (make-span :start (span->start peek-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-typedef
                  :type type-spec
                  :name (token-ident->ident name?))
                 span parstate)))
       ;; Otherwise: field or method (put first token back)
       ((unless peek-token?)
        ;; EOF where we expected a member — report the error
        (reterr-msg :where (span->start peek-span)
                    :expected "class member declaration or '}'"
                    :found peek-token?
                    :extra nil))
       (parstate (unread-token parstate)))
    (parse-cpp-member-field-or-method parstate))

  ///

  (defret parsize-of-parse-cpp-member-decl-item-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-member-decl-item-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :use ((:instance parsize-of-parse-cpp-member-access-label-cond)
                   (:instance parsize-of-parse-cpp-using-decl-cond)
                   (:instance parsize-of-parse-cpp-enum-decl-cond)
                   (:instance parsize-of-parse-cpp-member-field-or-method-cond))
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Declaration List Body
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-decl-list-body ((parstate parstatep))
  :returns (mv erp
               (decls cpp-member-decl-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :short "Parse a sequence of C++ class member declarations until @('}') is peeked."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads member declarations one by one until the next token is @('}') or EOF.
     Returns the accumulated list and the span of the last member parsed.
     The @('}') token is NOT consumed; the caller is responsible for reading it."))
  (b* (((reterr) nil (irr-span) parstate)
       ;; Peek to see if we've reached the end of the class body
       ((erp peek-token? peek-span parstate) (read-token parstate))
       ((when (or (not peek-token?)
                  (token-punctuatorp peek-token? "}")))
        ;; End of body — put the token back and return empty list
        (b* ((parstate (if peek-token? (unread-token parstate) parstate)))
          (retok nil peek-span parstate)))
       ;; Not end — put peek back and parse one member
       (parstate (unread-token parstate))
       ((erp decl decl-span parstate) (parse-cpp-member-decl-item parstate))
       ;; Recurse for the rest
       ((erp rest & parstate) (parse-cpp-member-decl-list-body parstate)))
    (retok (cons decl rest) decl-span parstate))

  ///

  (defret parsize-of-parse-cpp-member-decl-list-body-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-member-decl-list-body parstate)
             :in-theory (enable parsize-of-parse-cpp-member-decl-item-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Class Specifier
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-class-specifier ((parstate parstatep))
  :returns (mv erp
               (cls cpp-class-specifier-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ class specifier: @('class-head { members }')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses @('class-key [name] [< template-params >] [: base-clause] { members }').")
   (xdoc::p
    "The class-key is @('class') or @('struct').
     The name is optional (anonymous classes).
     The template parameter list is optional.
     The base clause (starting with @(':')) is optional.
     The body is a sequence of member declarations."))
  (b* (((reterr) (irr-cpp-class-specifier) (irr-span) parstate)
       ;; Read the class key
       ((erp key key-span parstate) (parse-cpp-class-key parstate))
       ;; Optional: class name identifier
       ((erp name-token? & parstate) (read-token parstate))
       ;; Determine if the token is actually a class name (not '{', '<', ':')
       (name-p (and name-token?
                    (token-case name-token? :ident)
                    (not (token-punctuatorp name-token? "{"))
                    (not (token-punctuatorp name-token? "<"))
                    (not (token-punctuatorp name-token? ":"))))
       (class-name (if name-p (token-ident->ident name-token?) nil))
       ;; If not a name token, put it back
       (parstate (if (and name-token? (not name-p))
                     (unread-token parstate)
                   parstate))
       ;; Optional: template parameter list '<' ... '>'
       ((erp tmpl-token? & parstate) (read-token parstate))
       ((mv template-params parstate)
        (cond
         ((token-punctuatorp tmpl-token? "<")
          (b* ((parstate (unread-token parstate))
               ((mv erp2 params & parstate) (parse-cpp-template-param-list parstate)))
            (if erp2 (mv nil parstate) (mv params parstate))))
         (tmpl-token?
          (let* ((parstate (unread-token parstate)))
            (mv nil parstate)))
         (t (mv nil parstate))))
       ;; Optional: base clause ':'
       ((erp colon-token? & parstate) (read-token parstate))
       ((mv bases parstate)
        (cond
         ((token-punctuatorp colon-token? ":")
          (b* ((parstate (unread-token parstate))
               ((mv erp2 base-list & parstate) (parse-cpp-base-clause parstate)))
            (if erp2 (mv nil parstate) (mv base-list parstate))))
         (colon-token?
          (let* ((parstate (unread-token parstate)))
            (mv nil parstate)))
         (t (mv nil parstate))))
       ;; Expect '{'
       ((erp open-token? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open-token? "{"))
        (reterr-msg :where (span->start open-span)
                    :expected "'{' to begin class body"
                    :found open-token?
                    :extra nil))
       ;; Parse member declarations
       ((erp members & parstate)
        (parse-cpp-member-decl-list-body parstate))
       ;; Expect '}'
       ((erp close-token? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close-token? "}"))
        (reterr-msg :where (span->start close-span)
                    :expected "'}' to end class body"
                    :found close-token?
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

  (defret parsize-of-parse-cpp-class-specifier-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Exception Handler Header
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-exception-handler-header ((parstate parstatep))
  :returns (mv erp
               (handler cpp-exception-handler-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ catch clause header: @('catch ( type-spec [param-name] )')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the @('catch') keyword (arriving as an identifier token)
     followed by @('('), the exception type specifier via
     @(tsee parse-cpp-type-spec),
     an optional parameter name identifier, and @(')').")
   (xdoc::p
    "The body of the catch clause (the @('{...}') block) is NOT parsed."))
  (b* (((reterr) (irr-cpp-exception-handler) (irr-span) parstate)
       ;; Read 'catch'
       ((erp catch-token? catch-span parstate) (read-token parstate))
       ((unless (token-cpp-kw-p catch-token? "catch"))
        (reterr-msg :where (span->start catch-span)
                    :expected "'catch' keyword"
                    :found catch-token?
                    :extra nil))
       ;; Read '('
       ((erp open-token? open-span parstate) (read-token parstate))
       ((unless (token-punctuatorp open-token? "("))
        (reterr-msg :where (span->start open-span)
                    :expected "'(' after 'catch'"
                    :found open-token?
                    :extra nil))
       ;; Parse exception type specifier
       ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
       ;; Optional: parameter name
       ((erp name-token? & parstate) (read-token parstate))
       (name-p (and name-token?
                    (token-case name-token? :ident)
                    (not (token-punctuatorp name-token? ")"))))
       (param-name (if name-p (token-ident->ident name-token?) nil))
       (parstate (if (and name-token? (not name-p))
                     (unread-token parstate)
                   parstate))
       ;; Read ')'
       ((erp close-token? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close-token? ")"))
        (reterr-msg :where (span->start close-span)
                    :expected "')' to close catch clause header"
                    :found close-token?
                    :extra nil))
       (span (make-span :start (span->start catch-span)
                        :end   (span->end close-span))))
    (retok (make-cpp-exception-handler :type-name  type-spec
                                       :param-name param-name)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-exception-handler-header-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-exception-handler-header-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Exception Handler List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-exception-handler-list ((parstate parstatep))
  :returns (mv erp
               (handlers cpp-exception-handler-listp)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :short "Parse a sequence of C++ catch clause headers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads catch clause headers one by one as long as the next token
     is the @('catch') keyword.
     The body (@('{...}')) of each catch clause is NOT parsed."))
  (b* (((reterr) nil (irr-span) parstate)
       ;; Peek at the next token
       ((erp peek-token? peek-span parstate) (read-token parstate))
       ((when (not (token-cpp-kw-p peek-token? "catch")))
        ;; Not a 'catch' — end of list
        (b* ((parstate (if peek-token? (unread-token parstate) parstate)))
          (retok nil peek-span parstate)))
       ;; Put back 'catch' and parse one handler header
       (parstate (unread-token parstate))
       ((erp handler handler-span parstate)
        (parse-cpp-exception-handler-header parstate))
       ;; Recurse for more handlers
       ((erp rest & parstate) (parse-cpp-exception-handler-list parstate)))
    (retok (cons handler rest) handler-span parstate))

  ///

  (defret parsize-of-parse-cpp-exception-handler-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-exception-handler-list parstate)
             :in-theory (enable parsize-of-parse-cpp-exception-handler-header-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Module Declaration Header
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-module-decl-header ((parstate parstatep))
  :returns (mv erp
               (decl cpp-module-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ module declaration header: @('[export] module [name]')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses @('[export] module [name]') stopping before the @(';').
     If @('export') appears first, @(':exportp') is @('t').
     @('module :') introduces the private module fragment (@(':private')).")
   (xdoc::p
    "The leading @('export') keyword, if present, must already be consumed
     by the caller or detected via a peek.
     This function reads starting from @('export') or @('module')."))
  (b* (((reterr) (irr-cpp-module-decl) (irr-span) parstate)
       ;; Read first token — may be 'export' or 'module'
       ((erp first-token? first-span parstate) (read-token parstate))
       ;; Detect optional 'export'
       ((mv exportp start-span parstate)
        (if (token-cpp-kw-p first-token? "export")
            ;; Consume 'export'; next should be 'module'
            (b* (((mv erp2 mod-token? & parstate) (read-token parstate)))
              (let* ((parstate (if (and (not erp2) mod-token?
                                        (not (token-cpp-kw-p mod-token? "module")))
                                   (unread-token parstate)
                                 parstate)))
                (mv t first-span parstate)))
          ;; First token is 'module' (or error)
          (mv nil first-span parstate)))
       ;; At this point the 'module' keyword was consumed above, OR
       ;; first-token? was 'module' and parstate is past it.
       ;; If first-token? was not 'export' and not 'module', error.
       ((when (and (not exportp)
                   (not (token-cpp-kw-p first-token? "module"))))
        (reterr-msg :where (span->start first-span)
                    :expected "'export' or 'module' keyword"
                    :found first-token?
                    :extra nil))
       ;; Peek at next token: could be ':', name ident, or ';'
       ((erp next-token? next-span parstate) (read-token parstate))
       ;; Private module fragment: 'module :' where next is ':'
       ((when (token-punctuatorp next-token? ":"))
        ;; Expect 'private' after ':'
        (b* (((erp priv-token? priv-span parstate) (read-token parstate))
             ((unless (token-cpp-kw-p priv-token? "private"))
              (reterr-msg :where (span->start priv-span)
                          :expected "'private' after 'module :'"
                          :found priv-token?
                          :extra nil))
             (span (make-span :start (span->start start-span)
                              :end   (span->end priv-span))))
          (retok (cpp-module-decl-private) span parstate)))
       ;; Named module: next token is a name identifier
       ((when (and next-token? (token-case next-token? :ident)))
        (b* ((name-ident (token-ident->ident next-token?))
             (span (make-span :start (span->start start-span)
                              :end   (span->end next-span))))
          (retok (make-cpp-module-decl-named :name (list name-ident)
                                             :exportp exportp)
                 span parstate)))
       ;; No name and not ':', put back next token
       (parstate (if next-token? (unread-token parstate) parstate))
       ;; Anonymous/bare 'module;' — represent as named with a dummy?
       ;; Better: error if we can't determine the name
       ((unless exportp)
        ;; 'module;' with no name is unusual; treat as private fragment
        (retok (cpp-module-decl-private) next-span parstate)))
    ;; 'export module;' — no name
    (retok (make-cpp-module-decl-named
            :name    nil
            :exportp t)
           next-span parstate))

  ///

  (defret parsize-of-parse-cpp-module-decl-header-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Import Declaration Header
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-import-decl-header ((parstate parstatep))
  :returns (mv erp
               (decl cpp-import-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ import declaration header: @('[export] import name')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses @('[export] import name') stopping before the @(';').
     Returns a @(tsee cpp-import-decl) with the module name and export flag."))
  (b* (((reterr) (irr-cpp-import-decl) (irr-span) parstate)
       ;; Read first token — may be 'export' or 'import'
       ((erp first-token? first-span parstate) (read-token parstate))
       ;; Detect optional 'export'
       ((mv exportp parstate)
        (if (token-cpp-kw-p first-token? "export")
            ;; Consume 'export'; next must be 'import'
            (b* (((mv erp2 imp-tok? & parstate) (read-token parstate)))
              (let* ((parstate (if (and (not erp2) imp-tok?
                                        (not (token-cpp-kw-p imp-tok? "import")))
                                   (unread-token parstate)
                                 parstate)))
                (mv t parstate)))
          ;; Check that first token is 'import'
          (mv nil parstate)))
       ;; If not exportp, first-token? must be 'import'
       ((when (and (not exportp)
                   (not (token-cpp-kw-p first-token? "import"))))
        (reterr-msg :where (span->start first-span)
                    :expected "'export' or 'import' keyword"
                    :found first-token?
                    :extra nil))
       ;; Read the module name identifier
       ((erp name-token? name-span parstate) (read-token parstate))
       ((unless (and name-token? (token-case name-token? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "module name identifier after 'import'"
                    :found name-token?
                    :extra nil))
       (name-ident (token-ident->ident name-token?))
       (span (make-span :start (span->start first-span)
                        :end   (span->end name-span))))
    (retok (make-cpp-import-decl :name    (list name-ident)
                                 :exportp exportp)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-import-decl-header-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-import-decl-header-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))
