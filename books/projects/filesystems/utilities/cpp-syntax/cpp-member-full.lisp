; C++ Syntax Extension for ACL2 Kestrel C Library
;
; Full class/member parser: parse-cpp-member-field-or-method-full,
; parse-cpp-member-decl-item-full, parse-cpp-member-decl-list-body-full,
; parse-cpp-class-specifier-full.
; Depends on cpp-expr-parser (the mutual-recursion block).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-expr-parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Directed token-kind lemmas: derive token-kind from specific predicates.
;; C$::TOKEN-KIND-POSSIBILITIES is a forward-chaining rule triggered by
;; (token-kind x) that splits into 6 cases.  These one-way rewrites are more
;; efficient: they fire only when a specific predicate is already known.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; token-cpp-kw-p checks (token-case token? :ident), so kind is :ident.
(defthm token-kind-ident-when-cpp-kw-p
  (implies (token-cpp-kw-p tok? kw)
           (equal (c$::token-kind tok?) :ident))
  :hints (("Goal" :in-theory (enable token-cpp-kw-p)))
  :rule-classes :rewrite)

;; token-punctuatorp checks (token-case token :punctuator), so kind is :punctuator.
(defthm token-kind-punctuator-when-punctuatorp
  (implies (c$::token-punctuatorp tok? s)
           (equal (c$::token-kind tok?) :punctuator))
  :hints (("Goal" :in-theory (enable c$::token-punctuatorp)))
  :rule-classes :rewrite)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper: read and accumulate optional specifiers for a member declaration.
;; Extracts the 7-specifier prefix so the main parser avoids a 2^7=128 case
;; explosion in its :returns proofs.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-specifier-flags ((parstate parstatep))
  :returns (mv erp
               (virtualp   booleanp)
               (explicitp  booleanp)
               (constexprp booleanp)
               (inlinep    booleanp)
               (staticp    booleanp)
               (mutablep   booleanp)
               (destructorp booleanp)
               (tok        token-optionp
                           :hints (("Goal"
                                    :in-theory
                                    (e/d (c$::token-optionp-of-read-token.token?)
                                         (c$::token-kind-possibilities)))))
               (tok-span   spanp
                           :hints (("Goal"
                                    :in-theory
                                    (e/d (c$::spanp-of-read-token.span)
                                         (c$::token-kind-possibilities)))))
               (new-parstate parstatep :hyp (parstatep parstate)
                             :hints (("Goal"
                                      :in-theory
                                      (e/d (c$::parstatep-of-read-token.new-parstate)
                                           (c$::token-kind-possibilities))))))
  :guard-hints (("Goal" :in-theory (disable c$::token-kind-possibilities)))
  :short "Read optional member-declaration specifiers and the first
          non-specifier token."
  (b* (((reterr) nil nil nil nil nil nil nil nil (irr-span) parstate)
       ((erp t1? t1-span parstate) (read-token parstate))
       ;; Optional specifiers: virtual, explicit, constexpr, inline, static, mutable
       (virtualp (token-cpp-kw-p t1? "virtual"))
       ((erp t1? t1-span parstate)
        (if virtualp (read-token parstate) (mv nil t1? t1-span parstate)))
       (explicitp (token-cpp-kw-p t1? "explicit"))
       ((erp t1? t1-span parstate)
        (if explicitp (read-token parstate) (mv nil t1? t1-span parstate)))
       (constexprp (token-cpp-kw-p t1? "constexpr"))
       ((erp t1? t1-span parstate)
        (if constexprp (read-token parstate) (mv nil t1? t1-span parstate)))
       (inlinep (token-keywordp t1? "inline"))
       ((erp t1? t1-span parstate)
        (if inlinep (read-token parstate) (mv nil t1? t1-span parstate)))
       (staticp (token-keywordp t1? "static"))
       (mutablep (and (not staticp) (token-cpp-kw-p t1? "mutable")))
       ((erp t1? t1-span parstate)
        (if (or staticp mutablep) (read-token parstate)
          (mv nil t1? t1-span parstate)))
       ;; Destructor: '~' prefix
       (destructorp (token-punctuatorp t1? "~"))
       ((erp t1? t1-span parstate)
        (if destructorp (read-token parstate) (mv nil t1? t1-span parstate))))
    (retok virtualp explicitp constexprp inlinep staticp mutablep destructorp
           t1? t1-span parstate))

  ///

  (defret parsize-of-parse-cpp-member-specifier-flags-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token)
                             (c$::token-kind-possibilities)))))

  ;; Auxiliary: if no first token, tok? is nil.
  ;; The :forward-chaining class fires after each simplification round
  ;; (including after :cases adds the nil-first-token hypothesis), adding
  ;; (equal tok? nil) to the context so the cond proof closes vacuously.
  (defthm tok-nil-when-first-read-nil-parse-cpp-member-specifier-flags
    (implies (not (mv-nth 1 (c$::read-token parstate)))
             (equal (mv-nth 8 (parse-cpp-member-specifier-flags parstate)) nil))
    :rule-classes ((:rewrite)
                   (:forward-chaining
                    :trigger-terms ((mv-nth 1 (c$::read-token parstate)))))
    :hints (("Goal"
             :in-theory (enable parse-cpp-member-specifier-flags
                                token-cpp-kw-p
                                c$::token-keywordp
                                c$::token-punctuatorp))))

  (defret parsize-of-parse-cpp-member-specifier-flags-cond
    (implies (and (not erp) tok)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-cond
                              c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              tok-nil-when-first-read-nil-parse-cpp-member-specifier-flags)
                             (c$::token-kind-possibilities))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full member field/method parser: like parse-cpp-member-field-or-method
;; but allows an inline method body @('{ ... }') in place of @(';').
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-field-or-method-full ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p
                     :hints (("Goal"
                              :in-theory (disable c$::token-kind-possibilities
                                                  cpp-member-decl-field-iff-congruence-on-constexprp
                                                  cpp-member-decl-field-iff-congruence-on-mutablep
                                                  cpp-member-decl-field-iff-congruence-on-staticp
                                                  cpp-member-decl-method-iff-congruence-on-const-qualp
                                                  cpp-member-decl-method-iff-congruence-on-constexprp
                                                  cpp-member-decl-method-iff-congruence-on-destructorp
                                                  cpp-member-decl-method-iff-congruence-on-explicitp
                                                  cpp-member-decl-method-iff-congruence-on-inlinep
                                                  cpp-member-decl-method-iff-congruence-on-pure-virtualp
                                                  cpp-member-decl-method-iff-congruence-on-staticp
                                                  cpp-member-decl-method-iff-congruence-on-virtualp))))
               (span spanp
                     :hints (("Goal"
                              :in-theory (disable c$::token-kind-possibilities
                                                  cpp-member-decl-field-iff-congruence-on-constexprp
                                                  cpp-member-decl-field-iff-congruence-on-mutablep
                                                  cpp-member-decl-field-iff-congruence-on-staticp
                                                  cpp-member-decl-method-iff-congruence-on-const-qualp
                                                  cpp-member-decl-method-iff-congruence-on-constexprp
                                                  cpp-member-decl-method-iff-congruence-on-destructorp
                                                  cpp-member-decl-method-iff-congruence-on-explicitp
                                                  cpp-member-decl-method-iff-congruence-on-inlinep
                                                  cpp-member-decl-method-iff-congruence-on-pure-virtualp
                                                  cpp-member-decl-method-iff-congruence-on-staticp
                                                  cpp-member-decl-method-iff-congruence-on-virtualp))))
               (new-parstate parstatep :hyp (parstatep parstate)
                             :hints (("Goal"
                                      :in-theory
                                      (e/d (parstatep-of-parse-cpp-member-specifier-flags.new-parstate
                                            parstatep-of-parse-cpp-type-spec.new-parstate
                                            parstatep-of-parse-cpp-param-list.new-parstate
                                            parstatep-of-parse-cpp-noexcept-spec.new-parstate
                                            parstatep-of-parse-cpp-member-ctor-or-dtor-full.new-parstate
                                            return-type-of-parse-cpp-block-item-list-body.new-parstate
                                            c$::parstatep-of-read-token.new-parstate
                                            c$::parstatep-of-unread-token)
                                           (c$::token-kind-possibilities
                                            cpp-member-decl-field-iff-congruence-on-constexprp
                                            cpp-member-decl-field-iff-congruence-on-mutablep
                                            cpp-member-decl-field-iff-congruence-on-staticp
                                            cpp-member-decl-method-iff-congruence-on-const-qualp
                                            cpp-member-decl-method-iff-congruence-on-constexprp
                                            cpp-member-decl-method-iff-congruence-on-destructorp
                                            cpp-member-decl-method-iff-congruence-on-explicitp
                                            cpp-member-decl-method-iff-congruence-on-inlinep
                                            cpp-member-decl-method-iff-congruence-on-pure-virtualp
                                            cpp-member-decl-method-iff-congruence-on-staticp
                                            cpp-member-decl-method-iff-congruence-on-virtualp))))))
  :guard-hints (("Goal" :in-theory (disable c$::token-kind-possibilities)))
  :short "Parse a C++ field or method, possibly with an inline body."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ;; Read optional specifiers (virtual, explicit, constexpr, inline,
       ;; static/mutable, ~) and the first non-specifier token.
       ((erp virtualp explicitp constexprp inlinep staticp mutablep destructorp
             t1? t1-span parstate)
        (parse-cpp-member-specifier-flags parstate))
       ;; Type specifier must start with ident or keyword
       ((unless (and t1? (or (token-case t1? :ident) (token-case t1? :keyword))))
        (reterr-msg :where (span->start t1-span)
                    :expected "type specifier in member declaration"
                    :found t1?
                    :extra nil))
       (parstate (unread-token parstate))
       ((erp type-spec & parstate) (parse-cpp-type-spec parstate))
       ((erp name? name-span parstate) (read-token parstate))
       ;; If next is '(' (no separate name), it's a constructor/destructor.
       ;; '(' (name?) is already consumed; parse-cpp-member-ctor-or-dtor-full
       ;; expects the '(' to be consumed since it calls parse-cpp-param-list
       ;; which expects '(' to have been consumed already.
       ((when (token-punctuatorp name? "("))
        (b* (((erp decl decl-span parstate)
              (parse-cpp-member-ctor-or-dtor-full
               type-spec virtualp staticp destructorp
               explicitp constexprp inlinep t1-span parstate)))
          (retok decl decl-span parstate)))
       ;; Normal field or method: name? should be an identifier
       ((unless (and name? (token-case name? :ident)))
        (reterr-msg :where (span->start name-span)
                    :expected "member name identifier"
                    :found name?
                    :extra nil))
       (name-ident (token-ident->ident name?))
       ((erp peek? & parstate) (read-token parstate))
       ;; Field case: not followed by '('
       ((when (not (token-punctuatorp peek? "(")))
        (b* (;; Check for optional array suffix: '[' [size] ']'
             ;; Handles 'T arr[N];' and 'T arr[];' member field declarations.
             ((erp final-type semi-span parstate)
              (if (not (token-punctuatorp peek? "["))
                  ;; No array: put peek? back, read ';'
                  (b* ((parstate (if peek? (unread-token parstate) parstate))
                       ((erp semi? semi-span parstate) (read-token parstate))
                       ((unless (token-punctuatorp semi? ";"))
                        (reterr-msg :where (span->start semi-span)
                                    :expected "';' after field declaration"
                                    :found semi?
                                    :extra nil)))
                    (retok type-spec semi-span parstate))
                ;; Array: peek? = '[' is consumed; parse size then ']', then ';'
                (b* (((erp sz? sz-span parstate) (read-token parstate))
                     ((when (token-punctuatorp sz? "]"))
                      ;; T[] — unsized array
                      (b* (((erp semi? semi-span parstate) (read-token parstate))
                           ((unless (token-punctuatorp semi? ";"))
                            (reterr-msg :where (span->start semi-span)
                                        :expected "';' after array field"
                                        :found semi?
                                        :extra nil)))
                        (retok (make-cpp-type-spec-array
                                :element type-spec
                                :size-p nil
                                :size (irr-cpp-const-expr))
                               semi-span parstate)))
                     ;; Size must be an integer constant or identifier
                     ((unless (or (and sz? (token-case sz? :ident))
                                  (and sz? (token-case sz? :const)
                                       (c$::const-case
                                        (c$::token-const->const sz?) :int))))
                      (reterr-msg :where (span->start sz-span)
                                  :expected "integer constant or identifier as array size"
                                  :found sz?
                                  :extra nil))
                     (size-expr
                      (if (token-case sz? :const)
                          (make-cpp-const-expr-int
                           :iconst (c$::const-int->iconst
                                    (c$::token-const->const sz?)))
                        (make-cpp-const-expr-ident
                         :name (token-ident->ident sz?))))
                     ((erp rb? rb-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp rb? "]"))
                      (reterr-msg :where (span->start rb-span)
                                  :expected "']' after array size"
                                  :found rb?
                                  :extra nil))
                     ((erp semi? semi-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi? ";"))
                      (reterr-msg :where (span->start semi-span)
                                  :expected "';' after array field declaration"
                                  :found semi?
                                  :extra nil)))
                  (retok (make-cpp-type-spec-array
                          :element type-spec
                          :size-p t
                          :size size-expr)
                         semi-span parstate))))
             (span (make-span :start (span->start t1-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-field
                  :type-name  final-type
                  :field-name name-ident
                  :staticp    staticp
                  :mutablep   mutablep
                  :constexprp constexprp)
                 span parstate)))
       ;; Method case: followed by '('
       ((erp params & parstate) (parse-cpp-param-list parstate))
       ((erp const? & parstate) (read-token parstate))
       (const-qualp (token-keywordp const? "const"))
       (parstate (if (and const? (not const-qualp))
                     (unread-token parstate) parstate))
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
         (t (if eq? (unread-token parstate) parstate))))
       ;; Now check for inline body '{' or ';'
       ((erp tail? tail-span parstate) (read-token parstate))
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
                  :return-type    type-spec
                  :method-id      (make-cpp-member-name-simple :id name-ident)
                  :params         params
                  :virtualp       virtualp
                  :const-qualp    const-qualp
                  :noexcept-spec  noexcept-spec
                  :pure-virtualp  pure-virtualp
                  :staticp        staticp
                  :body-p         t
                  :body           body
                  :destructorp    destructorp
                  :explicitp      explicitp
                  :constexprp     constexprp
                  :inlinep        inlinep
                  :ctor-init-p    nil
                  :ctor-init-list nil)
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
            :return-type    type-spec
            :method-id      (make-cpp-member-name-simple :id name-ident)
            :params         params
            :virtualp       virtualp
            :const-qualp    const-qualp
            :noexcept-spec  noexcept-spec
            :pure-virtualp  pure-virtualp
            :staticp        staticp
            :body-p         nil
            :body           nil
            :destructorp    destructorp
            :explicitp      explicitp
            :constexprp     constexprp
            :inlinep        inlinep
            :ctor-init-p    nil
            :ctor-init-list nil)
           span parstate))

  ///

  (defret parsize-of-parse-cpp-member-field-or-method-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-member-specifier-flags-uncond
                              parsize-of-parse-cpp-type-spec-uncond
                              parsize-of-parse-cpp-param-list-uncond
                              parsize-of-parse-cpp-noexcept-spec-uncond
                              parsize-of-parse-cpp-member-ctor-or-dtor-full-uncond
                              parsize-of-parse-cpp-block-item-list-body-uncond)
                             (c$::token-kind-possibilities)))))

  (defret parsize-of-parse-cpp-member-field-or-method-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-cond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-member-specifier-flags-uncond
                              parsize-of-parse-cpp-member-specifier-flags-cond
                              parsize-of-parse-cpp-type-spec-cond
                              parsize-of-parse-cpp-param-list-cond
                              parsize-of-parse-cpp-noexcept-spec-uncond
                              parsize-of-parse-cpp-member-ctor-or-dtor-full-cond
                              parsize-of-parse-cpp-block-item-list-body-uncond)
                             (c$::token-kind-possibilities))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full member-decl item: access label or field/method (with possible body).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-member-decl-item-full ((parstate parstatep))
  :returns (mv erp
               (decl cpp-member-decl-p
                     :hints (("Goal"
                              :in-theory (disable c$::token-kind-possibilities))))
               (span spanp
                     :hints (("Goal"
                              :in-theory (disable c$::token-kind-possibilities))))
               (new-parstate parstatep :hyp (parstatep parstate)
                             :hints (("Goal"
                                      :in-theory
                                      (e/d (c$::parstatep-of-read-token.new-parstate
                                            c$::parstatep-of-unread-token
                                            parstatep-of-parse-cpp-member-access-label.new-parstate
                                            parstatep-of-parse-cpp-using-decl.new-parstate
                                            parstatep-of-parse-cpp-enum-decl.new-parstate
                                            parstatep-of-parse-cpp-type-spec.new-parstate
                                            return-type-of-parse-cpp-expr.new-parstate
                                            parstatep-of-parse-cpp-member-field-or-method-full.new-parstate)
                                           (c$::token-kind-possibilities))))))
  :guard-hints (("Goal" :in-theory (disable c$::token-kind-possibilities)))
  :short "Parse one C++ class member declaration, allowing inline bodies."
  (b* (((reterr) (irr-cpp-member-decl) (irr-span) parstate)
       ((erp peek? peek-span parstate) (read-token parstate))
       ;; Access label: 'public', 'private', or 'protected'
       ((when (token-cpp-access-spec-p peek?))
        (b* ((parstate (unread-token parstate)))
          (parse-cpp-member-access-label parstate)))
       ((unless peek?)
        (reterr-msg :where (span->start peek-span)
                    :expected "class member declaration or '}'"
                    :found peek?
                    :extra nil))
       ;; Using declaration: 'using ...' (put peek? back; parse-cpp-using-decl reads it)
       ((when (token-cpp-kw-p peek? "using"))
        (b* ((parstate (unread-token parstate))
             ((erp decl span parstate) (parse-cpp-using-decl parstate)))
          (retok (make-cpp-member-decl-using-decl :decl decl) span parstate)))
       ;; Enum declaration: 'enum ...' (put peek? back; parse-cpp-enum-decl reads it)
       ((when (token-keywordp peek? "enum"))
        (b* ((parstate (unread-token parstate))
             ((erp def span parstate) (parse-cpp-enum-decl parstate)))
          (retok (make-cpp-member-decl-enum-decl :def def) span parstate)))
       ;; Friend declaration: 'friend' 'class'/'struct' type-spec ';'
       ((when (token-cpp-kw-p peek? "friend"))
        ;; peek? ('friend') is already consumed
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
       ((when (token-keywordp peek? "typedef"))
        ;; peek? ('typedef') is already consumed
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
       ;; static_assert ( cond [, msg] ) ;
       ((when (token-cpp-kw-p peek? "static_assert"))
        ;; peek? ('static_assert') is already consumed
        (b* (((erp lp? lp-span parstate) (read-token parstate))
             ((unless (token-punctuatorp lp? "("))
              (reterr-msg :where (span->start lp-span)
                          :expected "'(' after 'static_assert'"
                          :found lp?
                          :extra nil))
             ((erp cond-e & parstate) (parse-cpp-expr parstate))
             ((erp next? & parstate) (read-token parstate))
             ((mv msg-p msg parstate)
              (if (token-punctuatorp next? ",")
                  (b* (((mv msg-erp msg-tok & parstate) (read-token parstate))
                       ((when msg-erp)
                        (mv nil (c$::irr-ident) parstate)))
                    (if (and msg-tok (token-case msg-tok :ident))
                        (mv t (token-ident->ident msg-tok) parstate)
                      (b* ((parstate (if msg-tok
                                         (unread-token parstate)
                                       parstate)))
                        (mv nil (c$::irr-ident) parstate))))
                (b* ((parstate (if next?
                                   (unread-token parstate)
                                 parstate)))
                  (mv nil (c$::irr-ident) parstate))))
             ((erp rp? rp-span parstate) (read-token parstate))
             ((unless (token-punctuatorp rp? ")"))
              (reterr-msg :where (span->start rp-span)
                          :expected "')' to close static_assert"
                          :found rp?
                          :extra nil))
             ((erp semi? semi-span parstate) (read-token parstate))
             ((unless (token-punctuatorp semi? ";"))
              (reterr-msg :where (span->start semi-span)
                          :expected "';' after static_assert"
                          :found semi?
                          :extra nil))
             (span (make-span :start (span->start peek-span)
                              :end   (span->end semi-span))))
          (retok (make-cpp-member-decl-static-assert
                  :cond cond-e :msg-p msg-p :msg msg)
                 span parstate)))
       ;; [[attribute]] specifier: '[' '[' name [( name )] ']' ']'
       ((when (token-punctuatorp peek? "["))
        ;; peek? ('[') is already consumed; read the second '['
        (b* (((erp lbrack2? & parstate) (read-token parstate))
             ((unless (token-punctuatorp lbrack2? "["))
              ;; Not [[: put both tokens back and fall through to field/method
              (b* ((parstate (if lbrack2? (unread-token parstate) parstate))
                   (parstate (unread-token parstate)))
                (parse-cpp-member-field-or-method-full parstate)))
             ;; We have [[: parse attribute name
             ((erp name? name-span parstate) (read-token parstate))
             ((unless (and name? (token-case name? :ident)))
              (reterr-msg :where (span->start name-span)
                          :expected "attribute name inside [[ ]]"
                          :found name?
                          :extra nil))
             (attr-name (token-ident->ident name?))
             ;; Check for optional '(' arg ')'
             ((erp maybe-paren? & parstate) (read-token parstate))
             ((when (token-punctuatorp maybe-paren? "("))
              ;; Path: attribute has an argument
              (b* (((erp arg-tok & parstate) (read-token parstate))
                   ((unless (and arg-tok (token-case arg-tok :ident)))
                    (reterr-msg :where (span->start name-span)
                                :expected "identifier inside attribute argument"
                                :found arg-tok
                                :extra nil))
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
                   (span (make-span :start (span->start peek-span)
                                    :end   (span->end rb2-span))))
                (retok (make-cpp-member-decl-attribute
                        :name attr-name :arg-p t :arg (token-ident->ident arg-tok))
                       span parstate)))
             ;; No '(': put maybe-paren? back and read ']]'
             (parstate (if maybe-paren? (unread-token parstate) parstate))
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
             (span (make-span :start (span->start peek-span)
                              :end   (span->end rb2-span))))
          (retok (make-cpp-member-decl-attribute
                  :name attr-name :arg-p nil :arg (c$::irr-ident))
                 span parstate)))
       ;; Otherwise: field or method (put first token back)
       (parstate (unread-token parstate)))
    (parse-cpp-member-field-or-method-full parstate))

  ///

  (defret parsize-of-parse-cpp-member-decl-item-full-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-member-access-label-uncond
                              parsize-of-parse-cpp-using-decl-uncond
                              parsize-of-parse-cpp-enum-decl-uncond
                              parsize-of-parse-cpp-type-spec-uncond
                              parsize-of-parse-cpp-expr-uncond
                              parsize-of-parse-cpp-member-field-or-method-full-uncond)
                             (c$::token-kind-possibilities)))))

  (defret parsize-of-parse-cpp-member-decl-item-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :use ((:instance parsize-of-parse-cpp-member-access-label-cond)
                   (:instance parsize-of-parse-cpp-using-decl-cond)
                   (:instance parsize-of-parse-cpp-enum-decl-cond)
                   (:instance parsize-of-parse-cpp-member-field-or-method-full-cond)
                   (:instance parsize-of-parse-cpp-expr-cond))
             :in-theory (e/d (c$::parsize-of-read-token-cond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-member-access-label-uncond
                              parsize-of-parse-cpp-using-decl-uncond
                              parsize-of-parse-cpp-enum-decl-uncond
                              parsize-of-parse-cpp-type-spec-uncond
                              parsize-of-parse-cpp-expr-uncond
                              parsize-of-parse-cpp-member-field-or-method-full-uncond)
                             (c$::token-kind-possibilities))))))

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
             :in-theory (e/d (parsize-of-parse-cpp-member-decl-item-full-uncond
                              parsize-of-parse-cpp-member-decl-item-full-cond
                              c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token)
                             (c$::token-kind-possibilities))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Full class specifier: like parse-cpp-class-specifier, but its members
;; can have inline bodies.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-class-specifier-full ((parstate parstatep))
  :returns (mv erp
               (cls cpp-class-specifier-p
                    :hints (("Goal"
                             :in-theory (disable c$::token-kind-possibilities))))
               (span spanp
                    :hints (("Goal"
                             :in-theory (disable c$::token-kind-possibilities))))
               (new-parstate parstatep :hyp (parstatep parstate)
                             :hints (("Goal"
                                      :in-theory (disable c$::token-kind-possibilities)))))
  :guard-hints (("Goal" :in-theory (disable c$::token-kind-possibilities)))
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
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-class-key-uncond
                              parsize-of-parse-cpp-template-param-list-uncond
                              parsize-of-parse-cpp-base-clause-uncond
                              parsize-of-parse-cpp-member-decl-list-body-full-uncond)
                             (c$::token-kind-possibilities)))))

  (defret parsize-of-parse-cpp-class-specifier-full-cond
    (implies (not erp)
             (< (parsize new-parstate)
                (parsize parstate)))
    :rule-classes :linear
    :hints (("Goal"
             :in-theory (e/d (c$::parsize-of-read-token-cond
                              c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-class-key-uncond
                              parsize-of-parse-cpp-template-param-list-uncond
                              parsize-of-parse-cpp-base-clause-uncond
                              parsize-of-parse-cpp-member-decl-list-body-full-uncond)
                             (c$::token-kind-possibilities))))))
