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
;
; Phase 2 parse functions:
;  - parse-cpp-base-specifier         ([access] class-name)
;  - parse-cpp-base-clause            (: base-spec {, base-spec}*)
;  - parse-cpp-member-access-label    (access :)
;  - parse-cpp-member-field-or-method ([virtual][static] type name [(...)] [const] [noexcept] [=0] ;)
;  - parse-cpp-member-decl-item       (one member: access-label or field/method)
;  - parse-cpp-member-decl-list-body  (list of members until '}')
;  - parse-cpp-class-specifier        (class-head { members })
;  - parse-cpp-noexcept-spec          (noexcept [(true/false)])
;  - parse-cpp-exception-handler-header (catch ( type [name] ))
;  - parse-cpp-exception-handler-list (list of catch headers)
;  - parse-cpp-module-decl-header     ([export] module [name])
;  - parse-cpp-import-decl-header     ([export] import name)

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
;; Parse: Template Parameter
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-template-param ((parstate parstatep))
  :returns (mv erp
               (param cpp-template-param-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ template parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses either a type parameter (@('typename T') or @('class T'))
     or a non-type parameter (@('int N')).")
   (xdoc::p
    "Type parameters: the @('typename') or @('class') keyword is followed
     by an optional identifier (the parameter name).
     We read one more token; if it is an identifier (not a comma or @('>'))
     we take it as the parameter name.  Otherwise we put it back.")
   (xdoc::p
    "Non-type parameters: the type is given as a single identifier
     followed by the parameter name identifier.
     This simplified parsing handles only the common case @('int N')."))
  (b* (((reterr) (irr-cpp-template-param) (irr-span) parstate)
       ((erp first-token? first-span parstate) (read-token parstate))
       ;; Type parameter introduced by 'typename' or 'class'
       ((when (token-cpp-template-type-kw-p first-token?))
        (b* (;; Determine whether this is 'typename' or 'class'
             (typenamep (token-cpp-kw-p first-token? "typename"))
             ;; Optionally read parameter name
             ((erp name-token? name-span parstate) (read-token parstate))
             ((when (and name-token?
                         (token-case name-token? :ident)
                         ;; Not ',' or '>' which would end the parameter list
                         (not (token-punctuatorp name-token? ","))
                         (not (token-punctuatorp name-token? ">"))))
              ;; The name-token is the parameter name
              (b* ((name-ident (token-ident->ident name-token?))
                   (span (make-span :start (span->start first-span)
                                    :end   (span->end name-span))))
                (retok (make-cpp-template-param-type
                        :typenamep typenamep
                        :name name-ident)
                       span parstate)))
             ;; No parameter name — put back the token we just read
             (parstate (if name-token? (unread-token parstate) parstate)))
          (retok (make-cpp-template-param-type :typenamep typenamep :name nil)
                 first-span parstate)))
       ;; Non-type parameter: expect 'type-name param-name'
       ;; For the simplified case, we expect two identifiers.
       ((unless (and first-token? (token-case first-token? :ident)))
        (reterr-msg :where (span->start first-span)
                    :expected "template parameter (typename/class T or type name N)"
                    :found first-token?
                    :extra nil))
       (type-ident (token-ident->ident first-token?))
       ((erp name-token? name-span parstate) (read-token parstate))
       ((unless (and name-token? (token-case name-token? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "parameter name identifier after type in non-type template parameter"
                    :found name-token?
                    :extra nil))
       (param-ident (token-ident->ident name-token?))
       (span (make-span :start (span->start first-span)
                        :end   (span->end name-span))))
    (retok (make-cpp-template-param-nontype :type-name type-ident
                                            :param-name param-ident)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-template-param-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-template-param-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Template Parameter List
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

  :prepwork
  ((define parse-cpp-template-param-list-rest ((open-span spanp)
                                               (parstate parstatep))
     :returns (mv erp
                  (params cpp-template-param-listp)
                  (close-span spanp)
                  (new-parstate parstatep :hyp (parstatep parstate)))
     :measure (parsize parstate)
     :parents nil
     (b* (((reterr) nil (irr-span) parstate)
          ;; Parse one parameter
          ((erp param & parstate) (parse-cpp-template-param parstate))
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
       (retok (cons param rest-params) close-span parstate))

     ///

     (defret parsize-of-parse-cpp-template-param-list-rest-uncond
       (<= (parsize new-parstate)
           (parsize parstate))
       :rule-classes :linear
       :hints (("Goal"
                :induct (parse-cpp-template-param-list-rest open-span parstate)
                :in-theory (enable parsize-of-parse-cpp-template-param-cond))))

     (defret parsize-of-parse-cpp-template-param-list-rest-cond
       (implies (not erp)
                (< (parsize new-parstate)
                   (parsize parstate)))
       :rule-classes :linear
       :hints (("Goal"
                :induct (parse-cpp-template-param-list-rest open-span parstate)
                :in-theory (enable parsize-of-parse-cpp-template-param-cond))))))

  ///

  (defret parsize-of-parse-cpp-template-param-list-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
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
          (retok (cpp-namespace-def-anonymous) ns-span parstate)))
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
          (retok (make-cpp-namespace-def-nested
                  :names (cons first-name rest-names))
                 span parstate)))
       ;; Single named namespace — put back sep-token?
       (parstate (if sep-token? (unread-token parstate) parstate))
       (span (make-span :start (span->start ns-span)
                        :end   (span->end next-span))))
    (retok (make-cpp-namespace-def-named :name first-name) span parstate))

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
;; Parse: Base Specifier (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helper: parse one base specifier: [access-spec] class-name
(define parse-cpp-base-specifier ((parstate parstatep))
  :returns (mv erp
               (spec cpp-base-specifier-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a single C++ base class specifier: @('[access] class-name')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses an optional access specifier (@('public'), @('private'),
     or @('protected')) followed by the base class name identifier.
     If no access specifier is present, defaults to @('public')."))
  (b* (((reterr) (irr-cpp-base-specifier) (irr-span) parstate)
       ;; Read the first token — may be an access specifier or the class name
       ((erp first-token? first-span parstate) (read-token parstate))
       ;; Check if the first token is an access specifier
       ((when (token-cpp-access-spec-p first-token?))
        (b* ((access (token-to-cpp-access-spec first-token?))
             ;; Read the class name
             ((erp name-token? name-span parstate) (read-token parstate))
             ((unless (and name-token? (token-case name-token? :ident)))
              (reterr-msg :where (span->start name-span)
                          :expected "class name identifier in base specifier"
                          :found name-token?
                          :extra nil))
             (class-name (token-ident->ident name-token?))
             (span (make-span :start (span->start first-span)
                              :end   (span->end name-span))))
          (retok (make-cpp-base-specifier :access access
                                          :class-name class-name)
                 span parstate)))
       ;; No access specifier — first token must be the class name
       ((unless (and first-token? (token-case first-token? :ident)))
        (reterr-msg :where (span->start first-span)
                    :expected "access specifier or class name in base specifier"
                    :found first-token?
                    :extra nil))
       (class-name (token-ident->ident first-token?)))
    ;; Default access: public
    (retok (make-cpp-base-specifier :access (cpp-access-spec-public)
                                    :class-name class-name)
           first-span parstate))

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
;; Parse: Base Clause (Phase 2)
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
;; Parse: Member Access Label (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
;; Parse: Parameter Count Helpers (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursive helper: scan from the first non-'(' token until ')',
;; counting comma-separated parameters.
(define parse-cpp-param-count-rest ((acc natp) (parstate parstatep))
  :returns (mv erp
               (count natp)
               (close-span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :measure (parsize parstate)
  :parents nil
  :short "Continue scanning parameters after the first token has been seen."
  (b* (((reterr) 0 (irr-span) parstate)
       ((erp tok? tok-span parstate) (read-token parstate))
       ;; ')' ends the param list
       ((when (token-punctuatorp tok? ")"))
        (retok (nfix acc) tok-span parstate))
       ;; ',' separates parameters
       ((when (token-punctuatorp tok? ","))
        (parse-cpp-param-count-rest (1+ (nfix acc)) parstate))
       ;; Any other token: keep scanning
       ((unless tok?)
        (reterr-msg :where (span->start tok-span)
                    :expected "')' to close parameter list"
                    :found tok?
                    :extra nil)))
    (parse-cpp-param-count-rest (nfix acc) parstate))

  ///

  (defret parsize-of-parse-cpp-param-count-rest-uncond
    (<= (parsize new-parstate) (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param-count-rest acc parstate)
             :in-theory (enable c$::parsize-of-read-token-cond))))

  (defret parsize-of-parse-cpp-param-count-rest-cond
    (implies (not erp)
             (< (parsize new-parstate) (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :induct (parse-cpp-param-count-rest acc parstate)
             :in-theory (enable c$::parsize-of-read-token-cond)))))

;; Non-recursive entry point: consume tokens from after '(' until ')'.
(define parse-cpp-param-count ((parstate parstatep))
  :returns (mv erp
               (count natp)
               (close-span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :parents nil
  :short "Scan past parameters to @(')') counting comma-separated parameters."
  (b* (((reterr) 0 (irr-span) parstate)
       ;; Peek at the first token inside '('
       ((erp tok? tok-span parstate) (read-token parstate))
       ;; Empty param list: immediate ')'
       ((when (token-punctuatorp tok? ")"))
        (retok 0 tok-span parstate))
       ;; End of file
       ((unless tok?)
        (reterr-msg :where (span->start tok-span)
                    :expected "')' or parameter tokens in parameter list"
                    :found tok?
                    :extra nil))
       ;; At least one parameter; scan the rest
       ((erp rest-count close-span parstate)
        (parse-cpp-param-count-rest 1 parstate)))
    (retok rest-count close-span parstate))

  ///

  (defret parsize-of-parse-cpp-param-count-uncond
    (<= (parsize new-parstate) (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-param-count-cond
    (implies (not erp)
             (< (parsize new-parstate) (parsize parstate)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Field or Method (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-field-or-method ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a simplified C++ member field or method declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a member declaration of the form:
     @('[virtual] [static|mutable] type-ident name-ident [( ... )] [const] [noexcept] [= 0] ;').")
   (xdoc::p
    "Strategy: read optional qualifiers (@('virtual'), @('static'), @('mutable')),
     then the type identifier, then the member name identifier.
     Peek at the next token: if @('('), it is a method; otherwise it is a field.
     For methods, scan past @('...') to @(')') counting parameters,
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
       (staticp (token-cpp-kw-p t1? "static"))
       (mutablep (and (not staticp) (token-cpp-kw-p t1? "mutable")))
       ((erp t1? t1-span parstate)
        (if (or staticp mutablep)
            (read-token parstate)
          (mv nil t1? t1-span parstate)))
       ;; --- Type identifier ---
       ((unless (and t1? (token-case t1? :ident)))
        (reterr-msg :where (span->start t1-span)
                    :expected "type identifier in member declaration"
                    :found t1?
                    :extra nil))
       (type-ident (token-ident->ident t1?))
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
                  :type-name  type-ident
                  :field-name name-ident
                  :staticp    staticp
                  :mutablep   mutablep)
                 span parstate)))
       ;; --- METHOD case: peek-token? = '(' ---
       ;; Scan tokens until matching ')'; count comma-separated params
       ((erp num-params & parstate) (parse-cpp-param-count parstate))
       ;; Check for 'const'
       ((erp const-token? & parstate) (read-token parstate))
       (const-qualp (token-keywordp const-token? "const"))
       (parstate (if (and const-token? (not const-qualp))
                     (unread-token parstate)
                   parstate))
       ;; Check for 'noexcept'
       ((erp noexcept-token? & parstate) (read-token parstate))
       (noexcept-p (token-cpp-noexcept-p noexcept-token?))
       (parstate (if (and noexcept-token? (not noexcept-p))
                     (unread-token parstate)
                   parstate))
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
          ;; Had '=' but zero-token? was not an integer: put both back
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
            :return-type   type-ident
            :method-name   name-ident
            :num-params    num-params
            :virtualp      virtualp
            :const-qualp   const-qualp
            :pure-virtualp pure-virtualp
            :staticp       staticp)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-member-field-or-method-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear)

  (defret parsize-of-parse-cpp-member-field-or-method-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Declaration Item (Phase 2)
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
                   (:instance parsize-of-parse-cpp-member-field-or-method-cond))
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Member Declaration List Body (Phase 2)
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
;; Parse: Class Specifier (Phase 2)
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
;; Parse: Noexcept Specifier (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-noexcept-spec ((parstate parstatep))
  :returns (mv erp
               (spec cpp-noexcept-spec-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ @('noexcept') specifier: @('noexcept') or @('noexcept(true/false)')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reads the @('noexcept') keyword.
     If the next token is @('('), reads @('true') or @('false') and @(')'),
     returning a @(':constant') noexcept spec.
     Otherwise, returns a @(':bare') noexcept spec."))
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
       ;; Read 'true' or 'false'
       ((erp bool-token? bool-span parstate) (read-token parstate))
       ((mv value ok)
        (cond ((token-keywordp bool-token? "true")  (mv t t))
              ((token-keywordp bool-token? "false") (mv nil t))
              (t (mv nil nil))))
       ((unless ok)
        (reterr-msg :where (span->start bool-span)
                    :expected "'true' or 'false' in noexcept()"
                    :found bool-token?
                    :extra nil))
       ;; Read ')'
       ((erp close-token? close-span parstate) (read-token parstate))
       ((unless (token-punctuatorp close-token? ")"))
        (reterr-msg :where (span->start close-span)
                    :expected "')' after noexcept(bool)"
                    :found close-token?
                    :extra nil))
       (span (make-span :start (span->start noex-span)
                        :end   (span->end close-span))))
    (retok (make-cpp-noexcept-spec-constant :value value) span parstate))

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
;; Parse: Exception Handler Header (Phase 2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-exception-handler-header ((parstate parstatep))
  :returns (mv erp
               (handler cpp-exception-handler-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a C++ catch clause header: @('catch ( type-name [param-name] )')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses the @('catch') keyword (arriving as an identifier token)
     followed by @('('), the exception type identifier,
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
       ;; Read exception type name
       ((erp type-token? type-span parstate) (read-token parstate))
       ((unless (and type-token? (token-case type-token? :ident)))
        (reterr-msg :where (span->start type-span)
                    :expected "exception type identifier in catch clause"
                    :found type-token?
                    :extra nil))
       (type-ident (token-ident->ident type-token?))
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
    (retok (make-cpp-exception-handler :type-name  type-ident
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
;; Parse: Exception Handler List (Phase 2)
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
;; Parse: Module Declaration Header (Phase 2)
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
          (retok (make-cpp-module-decl-named :name name-ident
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
            :name    (c$::irr-ident)
            :exportp t)
           next-span parstate))

  ///

  (defret parsize-of-parse-cpp-module-decl-header-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parse: Import Declaration Header (Phase 2)
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
    (retok (make-cpp-import-decl :name    name-ident
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
