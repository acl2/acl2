; C++ Syntax Extension for ACL2 Kestrel C Library
;
; Top-level declaration parser: dispatches on namespace/class/using/enum.
; Depends only on cpp-parser (not cpp-expr-parser), enabling parallel cert.
;
; Parse functions defined here:
;  - parse-cpp-top-level-decl        (namespace/class/using/enum/;)
;  - parse-cpp-namespace-full        (namespace hdr { body })
;  - parse-cpp-namespace-body        (body = top-level-decl-list)
;  - parse-cpp-top-level-decl-list-body (loop until EOF)
;  - parse-cpp-translation-unit      (full translation unit)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-member-full")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dotted Module Name Helper
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-module-name-rest ((parstate parstatep))
  :returns (mv erp
               (segs c$::ident-listp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse optional @('.ident') segments of a dotted C++ module name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Called after reading the first identifier of a module/import name.
     Repeatedly peeks for a @('.') token; if found, reads it and the
     following identifier, appending it to the result.
     Returns the list of additional identifier segments (not the first one).
     For example, for @('std.core'), called after reading @('std'),
     this returns @('(list core)')."))
  :measure (parsize parstate)
  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-read-token-uncond
                                     c$::parsize-of-unread-token)))
  (b* (((reterr) nil parstate)
       (psize (parsize parstate))
       ;; Peek for '.'
       ((erp dot? & parstate) (read-token parstate))
       ;; If not '.', put it back and return nothing (success, empty list)
       ((unless (token-punctuatorp dot? "."))
        (b* ((parstate (if dot? (unread-token parstate) parstate)))
          (retok nil parstate)))
       ;; Got '.', now read the next identifier (parstate is past the dot)
       ((erp seg? & parstate) (read-token parstate))
       ;; If not an ident, put back what we got (dot stays consumed) and return
       ((unless (and seg? (token-case seg? :ident)))
        (b* ((parstate (if seg? (unread-token parstate) parstate)))
          (retok nil parstate)))
       (seg (token-ident->ident seg?))
       ;; Assert measure decrease for ACL2 termination
       ((unless (mbt (< (parsize parstate) psize)))
        (retok (list seg) parstate))
       ;; Recurse for more '.ident' segments
       ((erp rest parstate) (parse-cpp-module-name-rest parstate)))
    (retok (cons seg rest) parstate))
  ///
  (defret parsize-of-parse-cpp-module-name-rest-uncond
    (<= (parsize new-parstate) (parsize parstate))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-uncond
                                       c$::parsize-of-unread-token)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-Level Declarations (mutually recursive with namespace definitions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The four functions in this block are mutually recursive:
;;   parse-cpp-top-level-decl-list-body (rank 0): loops, calls parse-cpp-top-level-decl
;;   parse-cpp-namespace-body           (rank 0): delegates to the list-body function
;;   parse-cpp-namespace-full           (rank 1): reads hdr + { + body + }
;;   parse-cpp-top-level-decl           (rank 1): dispatches on first token
;;
;; Measure: (two-nats-measure (parsize parstate) rank)
;;   - rank 0 functions are called by rank 1 functions after consuming '{',
;;     so parsize strictly decreases for those calls.
;;   - The loop in list-body calls parse-cpp-top-level-decl with the same parsize
;;     after unreading the peeked token, so we need rank(list-body) < rank(top-level-decl).
;;   - Hence: list-body and namespace-body at rank 0, the other two at rank 1.

(defines parse-cpp-top-level-mutual
  :short "Mutually recursive top-level declaration parsers."
  :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                     c$::parsize-of-unread-token
                                     parsize-of-parse-cpp-namespace-def-header-uncond
                                     parsize-of-parse-cpp-template-param-list-uncond)))
  :ruler-extenders :all

  (define parse-cpp-top-level-decl ((parstate parstatep))
    :returns (mv erp
                 (decl cpp-top-level-decl-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse one C++ top-level declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "Dispatches on the first token:
       @('namespace') → full namespace definition (recursive),
       @('class') / @('struct') → class specifier,
       @('using') → using declaration,
       @('enum') → enum declaration,
       @(';') → empty declaration."))
    :measure (two-nats-measure (parsize parstate) 1)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-top-level-decl) (irr-span) parstate)
         ((erp tok? tok-span parstate) (read-token parstate))
         ;; 'namespace' → namespace alias or namespace definition
         ;; Disambiguate by peeking: namespace NAME = ... → alias
         ((when (token-cpp-kw-p tok? "namespace"))
          (b* (((erp name? & parstate) (read-token parstate))
               ;; If name? is an ident, peek further for '='
               ((when (and name? (token-case name? :ident)))
                (b* ((alias-name (token-ident->ident name?))
                     ((erp eq? & parstate) (read-token parstate))
                     ;; If '=' found → namespace alias
                     ((when (token-punctuatorp eq? "="))
                      (b* (((erp first-id? first-span parstate) (read-token parstate))
                           ((unless (and first-id? (token-case first-id? :ident)))
                            (reterr-msg :where (span->start first-span)
                                        :expected "qualified name after '=' in namespace alias"
                                        :found first-id?
                                        :extra nil))
                           (first-id (token-ident->ident first-id?))
                           ;; Parse optional :: rest of qualified name
                           ;; The C$ lexer produces ':' as single-char, so '::' is two ':' tokens
                           ((erp colon1? & parstate) (read-token parstate))
                           ((mv rest-names parstate)
                            (if (token-punctuatorp colon1? ":")
                                (b* (((mv & colon2? & parstate) (read-token parstate)))
                                  (if (token-punctuatorp colon2? ":")
                                      ;; Have '::': parse rest of qualified name
                                      (b* (((mv erp3 rest & parstate)
                                            (parse-cpp-nested-namespace-names parstate)))
                                        (if erp3 (mv nil parstate) (mv rest parstate)))
                                    ;; Only one ':': unread colon2 and colon1
                                    (b* ((parstate (if colon2? (unread-token parstate) parstate))
                                         (parstate (unread-token parstate)))
                                      (mv nil parstate))))
                              ;; Not ':' at all: unread colon1 if non-nil
                              (b* ((parstate (if colon1? (unread-token parstate) parstate)))
                                (mv nil parstate))))
                           ((erp semi? semi-span parstate) (read-token parstate))
                           ((unless (token-punctuatorp semi? ";"))
                            (reterr-msg :where (span->start semi-span)
                                        :expected "';' after namespace alias definition"
                                        :found semi?
                                        :extra nil))
                           (span (make-span :start (span->start tok-span)
                                            :end   (span->end semi-span))))
                        (retok (make-cpp-top-level-decl-namespace-alias
                                :decl (make-cpp-namespace-alias
                                       :name alias-name
                                       :target (cons first-id rest-names)))
                               span parstate)))
                     ;; Not an alias: restore all peeked tokens and call namespace-full
                     (parstate (if eq? (unread-token parstate) parstate))
                     (parstate (unread-token parstate)) ; put name? back
                     (parstate (unread-token parstate)) ; put namespace back
                     ((erp ns-def ns-span parstate) (parse-cpp-namespace-full parstate)))
                  (retok (make-cpp-top-level-decl-namespace-def :def ns-def) ns-span parstate)))
               ;; name? is not an ident (e.g., '{' or EOF): restore and call namespace-full
               (parstate (if name? (unread-token parstate) parstate))
               (parstate (unread-token parstate)) ; put namespace back
               ((erp ns-def ns-span parstate) (parse-cpp-namespace-full parstate)))
            (retok (make-cpp-top-level-decl-namespace-def :def ns-def) ns-span parstate)))
         ;; 'class' or 'struct' → class specifier
         ((when (or (token-cpp-kw-p tok? "class")
                    (token-keywordp tok? "struct")))
          (b* ((parstate (unread-token parstate))
               ((erp cls cls-span parstate) (parse-cpp-class-specifier-full parstate)))
            (retok (make-cpp-top-level-decl-class-def :def cls) cls-span parstate)))
         ;; 'using' → using declaration
         ((when (token-cpp-kw-p tok? "using"))
          (b* ((parstate (unread-token parstate))
               ((erp decl decl-span parstate) (parse-cpp-using-decl parstate)))
            (retok (make-cpp-top-level-decl-using-decl :decl decl) decl-span parstate)))
         ;; 'enum' → enum declaration
         ((when (token-keywordp tok? "enum"))
          (b* ((parstate (unread-token parstate))
               ((erp def def-span parstate) (parse-cpp-enum-decl parstate)))
            (retok (make-cpp-top-level-decl-enum-def :def def) def-span parstate)))
         ;; 'static_assert' → static_assert declaration
         ((when (token-cpp-kw-p tok? "static_assert"))
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
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-top-level-decl-static-assert
                    :cond cond-e :msg-p msg-p :msg msg)
                   span parstate)))
         ;; 'module' → module declaration
         ((when (token-cpp-kw-p tok? "module"))
          (b* (((erp next? next-span parstate) (read-token parstate))
               ((when (and next? (token-case next? :ident)))
                ;; module NAME ;  (NAME may be dotted, e.g. 'std.core')
                (b* ((first-id (token-ident->ident next?))
                     ((erp rest-segs parstate) (parse-cpp-module-name-rest parstate))
                     (name (cons first-id rest-segs))
                     ((erp semi? semi-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi? ";"))
                      (reterr-msg :where (span->start semi-span)
                                  :expected "';' after module declaration"
                                  :found semi?
                                  :extra nil))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end semi-span))))
                  (retok (make-cpp-top-level-decl-module-decl
                          :decl (make-cpp-module-decl-named :name name :exportp nil))
                         span parstate)))
               ((when (token-punctuatorp next? ":"))
                ;; module : private ;
                (b* (((erp priv? priv-span parstate) (read-token parstate))
                     ((unless (token-cpp-kw-p priv? "private"))
                      (reterr-msg :where (span->start priv-span)
                                  :expected "'private' after 'module :'"
                                  :found priv?
                                  :extra nil))
                     ((erp semi? semi-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi? ";"))
                      (reterr-msg :where (span->start semi-span)
                                  :expected "';' after 'module : private'"
                                  :found semi?
                                  :extra nil))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end semi-span))))
                  (retok (make-cpp-top-level-decl-module-decl
                          :decl (cpp-module-decl-private))
                         span parstate))))
            (reterr-msg :where (span->start next-span)
                        :expected "module name or ':' after 'module'"
                        :found next?
                        :extra nil)))
         ;; 'import' → import declaration
         ((when (token-cpp-kw-p tok? "import"))
          (b* (((erp name-tok? name-span parstate) (read-token parstate))
               ((unless (and name-tok? (token-case name-tok? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "module name after 'import'"
                            :found name-tok?
                            :extra nil))
               (first-id (token-ident->ident name-tok?))
               ((erp rest-segs parstate) (parse-cpp-module-name-rest parstate))
               (name (cons first-id rest-segs))
               ((erp semi? semi-span parstate) (read-token parstate))
               ((unless (token-punctuatorp semi? ";"))
                (reterr-msg :where (span->start semi-span)
                            :expected "';' after import declaration"
                            :found semi?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-top-level-decl-import-decl
                    :decl (make-cpp-import-decl :name name :exportp nil))
                   span parstate)))
         ;; 'export' → export module or export import
         ((when (token-cpp-kw-p tok? "export"))
          (b* (((erp next? next-span parstate) (read-token parstate))
               ;; 'export module NAME ;'
               ((when (token-cpp-kw-p next? "module"))
                (b* (((erp mod-name? mod-span parstate) (read-token parstate))
                     ((unless (and mod-name? (token-case mod-name? :ident)))
                      (reterr-msg :where (span->start mod-span)
                                  :expected "module name after 'export module'"
                                  :found mod-name?
                                  :extra nil))
                     (first-id (token-ident->ident mod-name?))
                     ((erp rest-segs parstate) (parse-cpp-module-name-rest parstate))
                     (name (cons first-id rest-segs))
                     ((erp semi? semi-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi? ";"))
                      (reterr-msg :where (span->start semi-span)
                                  :expected "';' after 'export module NAME'"
                                  :found semi?
                                  :extra nil))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end semi-span))))
                  (retok (make-cpp-top-level-decl-module-decl
                          :decl (make-cpp-module-decl-named :name name :exportp t))
                         span parstate)))
               ;; 'export import NAME ;'
               ((when (token-cpp-kw-p next? "import"))
                (b* (((erp imp-name? imp-span parstate) (read-token parstate))
                     ((unless (and imp-name? (token-case imp-name? :ident)))
                      (reterr-msg :where (span->start imp-span)
                                  :expected "module name after 'export import'"
                                  :found imp-name?
                                  :extra nil))
                     (first-id (token-ident->ident imp-name?))
                     ((erp rest-segs parstate) (parse-cpp-module-name-rest parstate))
                     (name (cons first-id rest-segs))
                     ((erp semi? semi-span parstate) (read-token parstate))
                     ((unless (token-punctuatorp semi? ";"))
                      (reterr-msg :where (span->start semi-span)
                                  :expected "';' after 'export import NAME'"
                                  :found semi?
                                  :extra nil))
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end semi-span))))
                  (retok (make-cpp-top-level-decl-import-decl
                          :decl (make-cpp-import-decl :name name :exportp t))
                         span parstate))))
            (reterr-msg :where (span->start next-span)
                        :expected "'module' or 'import' after 'export'"
                        :found next?
                        :extra nil)))
         ;; 'template' → template specialization (template<>) or template decl (template<params>)
         ((when (token-cpp-kw-p tok? "template"))
          (b* ((psize (parsize parstate)) ; captured after consuming 'template'
               ;; Parse the full '<' params '>' parameter list
               ((erp params & parstate) (parse-cpp-template-param-list parstate))
               ;; MBT: '<' and '>' consumed; parsize strictly decreased from psize
               ((unless (mbt (< (parsize parstate) psize)))
                (reterr :impossible))
               ((erp inner-decl inner-span parstate)
                (parse-cpp-top-level-decl parstate))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end inner-span))))
            ;; Empty param list → explicit specialization; non-empty → template-decl
            (if (endp params)
                (retok (make-cpp-top-level-decl-template-specialization :decl inner-decl)
                       span parstate)
                (retok (make-cpp-top-level-decl-template-decl :params params :decl inner-decl)
                       span parstate))))
         ;; ';' → empty declaration
         ((when (token-punctuatorp tok? ";"))
          (retok (cpp-top-level-decl-empty) tok-span parstate))
         ;; 'typedef' → typedef declaration (tok? is already consumed)
         ((when (token-keywordp tok? "typedef"))
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
               (span (make-span :start (span->start tok-span)
                                :end   (span->end semi-span))))
            (retok (make-cpp-top-level-decl-func-or-var-decl
                    :decl (make-cpp-member-decl-typedef
                           :type type-spec
                           :name (token-ident->ident name?)))
                   span parstate)))
         ;; '[' → possibly [[attribute]] specifier at top level
         ((when (token-punctuatorp tok? "["))
          (b* (((erp lbrack2? & parstate) (read-token parstate))
               ((unless (token-punctuatorp lbrack2? "["))
                ;; Not [[: put both tokens back and fall through to catch-all
                (b* ((parstate (if lbrack2? (unread-token parstate) parstate))
                     (parstate (unread-token parstate))
                     ((erp decl decl-span parstate) (parse-cpp-member-field-or-method parstate)))
                  (retok (make-cpp-top-level-decl-func-or-var-decl :decl decl)
                         decl-span parstate)))
               ;; Have [[: parse attribute name
               ((erp name? name-span parstate) (read-token parstate))
               ((unless (and name? (token-case name? :ident)))
                (reterr-msg :where (span->start name-span)
                            :expected "attribute name inside [[ ]]"
                            :found name?
                            :extra nil))
               (attr-name (token-ident->ident name?))
               ;; Optional ( arg )
               ((erp maybe-paren? & parstate) (read-token parstate))
               ((when (token-punctuatorp maybe-paren? "("))
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
                     (span (make-span :start (span->start tok-span)
                                      :end   (span->end rb2-span))))
                  (retok (make-cpp-top-level-decl-func-or-var-decl
                          :decl (make-cpp-member-decl-attribute
                                 :name attr-name :arg-p t :arg (token-ident->ident arg-tok)))
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
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rb2-span))))
            (retok (make-cpp-top-level-decl-func-or-var-decl
                    :decl (make-cpp-member-decl-attribute
                           :name attr-name :arg-p nil :arg (c$::irr-ident)))
                   span parstate)))
         ;; 'extern' keyword → possibly extern linkage block: extern "C" { ... }
         ((when (token-keywordp tok? "extern"))
          (b* (((erp lit? & parstate) (read-token parstate))
               ((unless (and lit? (token-case lit? :string)))
                ;; Not a linkage spec: put lit? back, unread extern, fall through
                (b* ((parstate (if lit? (unread-token parstate) parstate))
                     (parstate (unread-token parstate))
                     ((erp decl decl-span parstate) (parse-cpp-member-field-or-method parstate)))
                  (retok (make-cpp-top-level-decl-func-or-var-decl :decl decl)
                         decl-span parstate)))
               ;; String literal found: expect '{' body '}'
               (linkage (c$::token-string->literal lit?))
               ((erp lbrace? lbrace-span parstate) (read-token parstate))
               ((unless (token-punctuatorp lbrace? "{"))
                (reterr-msg :where (span->start lbrace-span)
                            :expected "'{' after extern linkage specifier"
                            :found lbrace?
                            :extra nil))
               ((erp body & parstate) (parse-cpp-namespace-body parstate))
               ((erp rbrace? rbrace-span parstate) (read-token parstate))
               ((unless (token-punctuatorp rbrace? "}"))
                (reterr-msg :where (span->start rbrace-span)
                            :expected "'}' to close extern linkage block"
                            :found rbrace?
                            :extra nil))
               (span (make-span :start (span->start tok-span)
                                :end   (span->end rbrace-span))))
            (retok (make-cpp-top-level-decl-extern-linkage
                    :linkage linkage :body body)
                   span parstate)))
         ;; Unexpected end of file
         ((unless tok?)
          (reterr-msg :where (span->start tok-span)
                      :expected "top-level declaration"
                      :found tok?
                      :extra nil))
         ;; Catch-all: function or variable declaration
         (parstate (unread-token parstate))
         ((erp decl decl-span parstate) (parse-cpp-member-field-or-method parstate)))
      (retok (make-cpp-top-level-decl-func-or-var-decl :decl decl)
             decl-span parstate)))

  (define parse-cpp-namespace-full ((parstate parstatep))
    :returns (mv erp
                 (ns-def cpp-namespace-def-p)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse a complete C++ namespace definition: @('namespace hdr { body }')."
    :measure (two-nats-measure (parsize parstate) 0)
    :verify-guards nil
    (b* (((reterr) (irr-cpp-namespace-def) (irr-span) parstate)
         ;; Parse the header: 'namespace [name]'
         ((erp hdr hdr-span parstate) (parse-cpp-namespace-def-header parstate))
         (kind    (cpp-namespace-def->kind    hdr))
         (inlinep (cpp-namespace-def->inlinep hdr))
         ;; Read '{'
         ((erp lbrace? lbrace-span parstate) (read-token parstate))
         ((unless (token-punctuatorp lbrace? "{"))
          (reterr-msg :where (span->start lbrace-span)
                      :expected "'{' after namespace header"
                      :found lbrace?
                      :extra nil))
         ;; Parse body (list of top-level decls until '}')
         ((erp body & parstate) (parse-cpp-namespace-body parstate))
         ;; Read '}'
         ((erp rbrace? rbrace-span parstate) (read-token parstate))
         ((unless (token-punctuatorp rbrace? "}"))
          (reterr-msg :where (span->start rbrace-span)
                      :expected "'}' to close namespace body"
                      :found rbrace?
                      :extra nil))
         (span (make-span :start (span->start hdr-span)
                          :end   (span->end rbrace-span))))
      (retok (make-cpp-namespace-def :kind kind :inlinep inlinep :body body)
             span parstate)))

  (define parse-cpp-namespace-body ((parstate parstatep))
    :returns (mv erp
                 (decls cpp-top-level-decl-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse the body of a C++ namespace (delegates to list-body helper)."
    :measure (two-nats-measure (parsize parstate) 3)
    :verify-guards nil
    (parse-cpp-top-level-decl-list-body parstate))

  (define parse-cpp-top-level-decl-list-body ((parstate parstatep))
    :returns (mv erp
                 (decls cpp-top-level-decl-listp)
                 (span spanp)
                 (new-parstate parstatep :hyp (parstatep parstate)))
    :short "Parse top-level declarations until @('}') or EOF is peeked."
    :long
    (xdoc::topstring
     (xdoc::p
      "Reads one token to peek.
       If it is EOF or @('}'), puts it back and returns an empty list.
       Otherwise puts it back and calls @(tsee parse-cpp-top-level-decl)
       for one declaration, then recurs."))
    :measure (two-nats-measure (parsize parstate) 2)
    :verify-guards nil
    (b* (((reterr) nil (irr-span) parstate)
         (psize (parsize parstate))
         ;; Peek at next token
         ((erp peek? peek-span parstate) (read-token parstate))
         ;; Stop at EOF or '}'
         ((when (or (not peek?)
                    (token-punctuatorp peek? "}")))
          (b* ((parstate (if peek? (unread-token parstate) parstate)))
            (retok nil peek-span parstate)))
         ;; Put it back and parse one declaration
         (parstate (unread-token parstate))
         ((erp decl decl-span parstate) (parse-cpp-top-level-decl parstate))
         ;; MBT guard: parse-cpp-top-level-decl must have consumed at least one token.
         ((unless (mbt (< (parsize parstate) psize)))
          (reterr :impossible))
         ;; Recurse
         ((erp rest & parstate) (parse-cpp-top-level-decl-list-body parstate)))
      (retok (cons decl rest) decl-span parstate)))

  ///

  (defthm-parse-cpp-top-level-mutual-flag
    parsize-of-parse-cpp-top-level-mutual-uncond
    (defthm parsize-of-parse-cpp-top-level-decl-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-top-level-decl parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-top-level-decl)
    (defthm parsize-of-parse-cpp-namespace-full-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-namespace-full parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-namespace-full)
    (defthm parsize-of-parse-cpp-namespace-body-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-namespace-body parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-namespace-body)
    (defthm parsize-of-parse-cpp-top-level-decl-list-body-uncond
      (<= (parsize (mv-nth 3 (parse-cpp-top-level-decl-list-body parstate)))
          (parsize parstate))
      :rule-classes :linear
      :flag parse-cpp-top-level-decl-list-body)
    :hints (("Goal"
             :expand ((parse-cpp-top-level-decl parstate)
                      (parse-cpp-namespace-full parstate)
                      (parse-cpp-namespace-body parstate)
                      (parse-cpp-top-level-decl-list-body parstate))
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-read-token-uncond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-module-name-rest-uncond
                                parsize-of-parse-cpp-namespace-def-header-uncond
                                parsize-of-parse-cpp-class-specifier-full-uncond
                                parsize-of-parse-cpp-using-decl-uncond
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-enum-decl-uncond
                                parsize-of-parse-cpp-member-field-or-method-uncond
                                parsize-of-parse-cpp-nested-namespace-names-uncond))))

  (defthm-parse-cpp-top-level-mutual-flag
    parsize-of-parse-cpp-top-level-mutual-cond
    (defthm parsize-of-parse-cpp-top-level-decl-cond
      (implies (not (mv-nth 0 (parse-cpp-top-level-decl parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-top-level-decl parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-top-level-decl)
    (defthm parsize-of-parse-cpp-namespace-full-cond
      (implies (not (mv-nth 0 (parse-cpp-namespace-full parstate)))
               (< (parsize (mv-nth 3 (parse-cpp-namespace-full parstate)))
                  (parsize parstate)))
      :rule-classes :linear
      :flag parse-cpp-namespace-full)
    (defthm parsize-of-parse-cpp-namespace-body-cond-placeholder
      t :rule-classes nil :flag parse-cpp-namespace-body)
    (defthm parsize-of-parse-cpp-top-level-decl-list-body-cond-placeholder
      t :rule-classes nil :flag parse-cpp-top-level-decl-list-body)
    :hints (("Goal"
             :expand ((parse-cpp-top-level-decl parstate)
                      (parse-cpp-namespace-full parstate)
                      (parse-cpp-namespace-body parstate)
                      (parse-cpp-top-level-decl-list-body parstate))
             :in-theory (enable c$::parsize-of-read-token-cond
                                c$::parsize-of-read-token-uncond
                                c$::parsize-of-unread-token
                                parsize-of-parse-cpp-module-name-rest-uncond
                                parsize-of-parse-cpp-namespace-def-header-uncond
                                parsize-of-parse-cpp-class-specifier-full-uncond
                                parsize-of-parse-cpp-class-specifier-full-cond
                                parsize-of-parse-cpp-expr-uncond
                                parsize-of-parse-cpp-expr-cond
                                parsize-of-parse-cpp-using-decl-uncond
                                parsize-of-parse-cpp-using-decl-cond
                                parsize-of-parse-cpp-enum-decl-uncond
                                parsize-of-parse-cpp-enum-decl-cond
                                parsize-of-parse-cpp-member-field-or-method-uncond
                                parsize-of-parse-cpp-member-field-or-method-cond
                                parsize-of-parse-cpp-type-spec-uncond
                                parsize-of-parse-cpp-type-spec-cond
                                parsize-of-parse-cpp-nested-namespace-names-uncond
                                parsize-of-parse-cpp-nested-namespace-names-cond))))

  ;; Helper lemma for guard verification: parse-cpp-template-param-list returns
  ;; either NIL or a CONSP (follows from the type theorem)
  (local
   (defthm parse-cpp-template-param-list-nil-or-consp
     (let ((params (mv-nth 1 (parse-cpp-template-param-list parstate))))
       (or (not params) (consp params)))
     :hints (("Goal" :use cpp-template-param-listp-of-parse-cpp-template-param-list.params
              :in-theory (e/d (cpp-template-param-listp)
                              (cpp-template-param-listp-of-parse-cpp-template-param-list.params))))
     :rule-classes :type-prescription))

  (verify-guards parse-cpp-top-level-decl
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token
                                       parsize-of-parse-cpp-member-field-or-method-uncond
                                       parsize-of-parse-cpp-template-param-list-uncond
                                       parsize-of-parse-cpp-template-param-list-cond)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Translation Unit Parser
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parse-cpp-translation-unit ((parstate parstatep))
  :returns (mv erp
               (tu cpp-translation-unit-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  :short "Parse a complete C++ translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "Parses a sequence of top-level declarations until EOF,
     wrapping the result in a @(tsee cpp-translation-unit)."))
  (b* (((reterr) (irr-cpp-translation-unit) (irr-span) parstate)
       ((erp decls decls-span parstate)
        (parse-cpp-top-level-decl-list-body parstate)))
    (retok (make-cpp-translation-unit :decls decls) decls-span parstate))

  ///

  (defret parsize-of-parse-cpp-translation-unit-uncond
    (<= (parsize new-parstate)
        (parsize parstate))
    :rule-classes :linear))
