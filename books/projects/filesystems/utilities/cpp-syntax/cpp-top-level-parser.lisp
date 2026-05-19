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

(include-book "cpp-parser")

;; Cond parsize bound for parse-cpp-class-specifier.
;; Not included in cpp-parser.lisp; proved here as a standalone theorem.
(defthm parsize-of-parse-cpp-class-specifier-cond
  (implies (not (mv-nth 0 (parse-cpp-class-specifier parstate)))
           (< (parsize (mv-nth 3 (parse-cpp-class-specifier parstate)))
              (parsize parstate)))
  :rule-classes :linear
  :hints (("Goal"
           :expand (parse-cpp-class-specifier parstate)
           :in-theory (enable c$::parsize-of-read-token-cond
                              c$::parsize-of-read-token-uncond
                              c$::parsize-of-unread-token
                              parsize-of-parse-cpp-class-key-cond
                              parsize-of-parse-cpp-class-key-uncond
                              parsize-of-parse-cpp-template-param-list-uncond
                              parsize-of-parse-cpp-base-clause-uncond
                              parsize-of-parse-cpp-member-decl-list-body-uncond))))

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
                                     parsize-of-parse-cpp-namespace-def-header-uncond)))
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
         ;; 'namespace' → full namespace definition
         ((when (token-cpp-kw-p tok? "namespace"))
          (b* ((parstate (unread-token parstate))
               ((erp ns-def ns-span parstate) (parse-cpp-namespace-full parstate)))
            (retok (make-cpp-top-level-decl-namespace-def :def ns-def) ns-span parstate)))
         ;; 'class' or 'struct' → class specifier
         ((when (or (token-cpp-kw-p tok? "class")
                    (token-keywordp tok? "struct")))
          (b* ((parstate (unread-token parstate))
               ((erp cls cls-span parstate) (parse-cpp-class-specifier parstate)))
            (retok (make-cpp-top-level-decl-class-def :def cls) cls-span parstate)))
         ;; 'using' → using declaration
         ((when (token-cpp-kw-p tok? "using"))
          (b* ((parstate (unread-token parstate))
               ((erp decl decl-span parstate) (parse-cpp-using-decl parstate)))
            (retok (make-cpp-top-level-decl-using-decl :decl decl) decl-span parstate)))
         ;; 'enum' → enum declaration
         ((when (token-cpp-kw-p tok? "enum"))
          (b* ((parstate (unread-token parstate))
               ((erp def def-span parstate) (parse-cpp-enum-decl parstate)))
            (retok (make-cpp-top-level-decl-enum-def :def def) def-span parstate)))
         ;; ';' → empty declaration
         ((when (token-punctuatorp tok? ";"))
          (retok (cpp-top-level-decl-empty) tok-span parstate))
         ;; Unexpected token
         ((unless tok?)
          (reterr-msg :where (span->start tok-span)
                      :expected "top-level declaration"
                      :found tok?
                      :extra nil)))
      (reterr-msg :where (span->start tok-span)
                  :expected "'namespace', 'class', 'struct', 'using', 'enum', or ';'"
                  :found tok?
                  :extra nil)))

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
                                parsize-of-parse-cpp-namespace-def-header-uncond
                                parsize-of-parse-cpp-class-specifier-uncond
                                parsize-of-parse-cpp-using-decl-uncond
                                parsize-of-parse-cpp-enum-decl-uncond))))

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
                                parsize-of-parse-cpp-namespace-def-header-uncond
                                parsize-of-parse-cpp-class-specifier-uncond
                                parsize-of-parse-cpp-class-specifier-cond
                                parsize-of-parse-cpp-using-decl-uncond
                                parsize-of-parse-cpp-using-decl-cond
                                parsize-of-parse-cpp-enum-decl-uncond
                                parsize-of-parse-cpp-enum-decl-cond))))

  (verify-guards parse-cpp-top-level-decl
    :hints (("Goal" :in-theory (enable c$::parsize-of-read-token-cond
                                       c$::parsize-of-unread-token)))))

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
