; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FUTHARK")

(include-book "grammar")
(include-book "lexical-syntax")

(include-book "kestrel/lists-light/len" :dir :system)
(include-book "projects/abnf/parsing-tools/defdefparse" :dir :system)
(include-book "projects/abnf/tree-operations/tree-utilities" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parser
  :parents (concrete-syntax parsing-and-printing)
  :short "Executable CST parser for the Remora-emitted Futhark IR subset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This parser follows the Remora front end pattern: parsing produces
     ABNF concrete syntax trees, and @(see syntax-abstraction) maps those
     trees to the FTY abstract syntax.")
   (xdoc::p
    "The nonrecursive lexical pieces are generated from @(tsee *grammar*)
     by @(tsee abnf::defdefparse).  Recursive syntactic pieces such as
     types, expressions, bodies, and declarations are hand-written because
     the current ABNF parser generator does not define mutually recursive
     parsing functions.")
   (xdoc::p
    "The parser input is a list of Unicode code points.  Public string
     decoding is handled by @(see parser-interface).")
   (xdoc::p
    "The hand-written mutually recursive parsers use length-based measures
     and flag-style return lemmas, following the Remora parser organization."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix)))

(local
 (defthm nfix-of-len
   (equal (nfix (len x)) (len x))
   :hints (("Goal" :in-theory (enable nfix)))))

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    abnf::tree-listp-when-result-not-error
                    acl2::nat-listp-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; b* binders for parsing functions.

(def-b*-binder pok
  :short "Check and propagate error results of parsing functions."
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv pok-fresh-var input)
         ,(car acl2::forms))
        ((when (reserrp pok-fresh-var))
         (mv (reserrf-push pok-fresh-var) input))
        (,(car args) pok-fresh-var))
     ,acl2::rest-expr))

(def-b*-binder pok<
  :short "Like @(tsee patbind-pok), but require strict input consumption."
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* (((mv pok-fresh-var input1)
         ,(car acl2::forms))
        ((when (reserrp pok-fresh-var))
         (mv (reserrf-push pok-fresh-var) input1))
        ((unless (mbt (< (len input1) (len input))))
         (mv (reserrf :impossible) input1))
        (input input1)
        (,(car args) pok-fresh-var))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generated lexical parsers.

(defsection parse-generation-macros
  :short "Parsing generation macros specialized to this parser."

  (abnf::defdefparse ir
    :package "FUTHARK"
    :grammar *grammar*
    :prefix parse))

(defsection parse-generation-tables
  :short "ABNF group and repetition tables for generated lexical parsers."

  (defparse-ir-group-table
    "( ascii-space / line-comment )" group-ws-item)

  (defparse-ir-option-table)

  (defparse-ir-repetition-table
    "*( ascii-space / line-comment )" repetition-*-ws-item))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Hand-written lexical pieces.

(define ascii-space-codepointp ((nat natp))
  :returns (yes/no booleanp)
  (b* ((nat (nfix nat)))
    (or (eql nat #x09)
        (eql nat #x0A)
        (eql nat #x0B)
        (eql nat #x0C)
        (eql nat #x0D)
        (eql nat #x20))))

(define parse-ascii-space ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "ascii-space: end of input") nil))
       (nat (car input))
       ((unless (ascii-space-codepointp nat))
        (mv (reserrf "ascii-space: not an ASCII whitespace code point")
            input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "ascii-space")
         :branches (list (list (abnf::tree-leafterm (list nat)))))
        (cdr input)))
  ///

  (defret len-of-parse-ascii-space-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-ascii-space-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(define line-comment-charp ((nat natp))
  :returns (yes/no booleanp)
  (b* ((nat (nfix nat)))
    (or (<= nat #x09)
        (and (<= #x0B nat) (<= nat #x0C))
        (and (<= #x0E nat) (<= nat #xD7FF))
        (and (<= #xE000 nat) (<= nat #x10FFFF)))))

(define parse-line-comment-rest ((input nat-listp))
  :returns (mv (chars nat-listp)
               (rest-input nat-listp))
  :measure (len (nat-list-fix input))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input)) (mv nil nil))
       (nat (car input))
       ((when (or (eql nat #x0A)
                  (eql nat #x0D)))
        (mv (list nat) (cdr input)))
       ((unless (line-comment-charp nat))
        (mv nil input))
       ((mv chars rest-input) (parse-line-comment-rest (cdr input))))
    (mv (cons nat chars) rest-input))
  ///

  (defret len-of-parse-line-comment-rest-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(define parse-line-comment ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* (((mv dashdash input) (abnf::parse-schars "--" input))
       ((when (reserrp dashdash)) (mv (reserrf-push dashdash) input))
       ((mv chars input) (parse-line-comment-rest input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "line-comment")
         :branches (list (list (abnf::tree-leafterm
                                (list* #x2D #x2D chars)))))
        input))
  ///

  (defret len-of-parse-line-comment-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-line-comment-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(defparse-ir-group "( ascii-space / line-comment )")
(defparse-ir-*-group "( ascii-space / line-comment )")
(defparse-ir-rulename "ws")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Words, names, and string literals.

(define parse-word-rest ((input nat-listp))
  :returns (mv (chars nat-listp)
               (rest-input nat-listp))
  :measure (len (nat-list-fix input))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input)) (mv nil nil))
       (nat (car input))
       ((unless (ir-word-char-codepointp nat))
        (mv nil input))
       ((mv chars rest-input) (parse-word-rest (cdr input))))
    (mv (cons nat chars) rest-input))
  ///

  (defret len-of-parse-word-rest-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(define parse-word ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "word: end of input") nil))
       (nat (car input))
       ((unless (ir-word-char-codepointp nat))
        (mv (reserrf "word: not a word character") input))
       ((mv chars rest-input) (parse-word-rest (cdr input))))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "word")
         :branches (list (list (abnf::tree-leafterm
                                (cons nat chars)))))
        rest-input))
  ///

  (defret len-of-parse-word-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-word-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(define parse-name ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* (((pok word) (parse-word input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "name")
         :branches (list (list word)))
        input))
  ///

  (defret len-of-parse-name-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-name-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(define parse-string-lit-rest ((input nat-listp))
  :returns (mv (chars acl2::nat-list-resultp)
               (rest-input nat-listp))
  :measure (len (nat-list-fix input))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "string-lit: unterminated string") nil))
       (nat (car input))
       ((when (eql nat #x22))
        (mv (list nat) (cdr input)))
       ((when (eql nat #x5C))
        (b* (((when (endp (cdr input)))
              (mv (reserrf "string-lit: unterminated escape") input))
             ((mv chars rest-input) (parse-string-lit-rest (cddr input)))
             ((when (reserrp chars))
              (mv (reserrf-push chars) rest-input)))
          (mv (cons nat (cons (cadr input) chars)) rest-input)))
       ((unless (ir-string-char-codepointp nat))
        (mv (reserrf (list :string-lit-invalid-raw-codepoint nat))
            input))
       ((mv chars rest-input) (parse-string-lit-rest (cdr input)))
       ((when (reserrp chars))
        (mv (reserrf-push chars) rest-input)))
    (mv (cons nat chars) rest-input))
  ///

  (defret len-of-parse-string-lit-rest-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear))

(define parse-string-lit ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :hooks (:fix)
  (b* ((input (nat-list-fix input))
       ((when (endp input))
        (mv (reserrf "string-lit: end of input") nil))
       ((unless (eql (car input) #x22))
        (mv (reserrf "string-lit: expected opening double quote") input))
       ((mv chars rest-input) (parse-string-lit-rest (cdr input)))
       ((when (reserrp chars))
        (mv (reserrf-push chars) rest-input)))
    (mv (abnf::make-tree-nonleaf
         :rulename? (abnf::rulename "string-lit")
         :branches (list (list (abnf::tree-leafterm
                                (cons #x22 chars)))))
        rest-input))
  ///

  (defret len-of-parse-string-lit-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-string-lit-<
    (implies (not (reserrp tree))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CST construction and token helpers.

(define make-cst ((rulename stringp) (children abnf::tree-listp))
  :returns (tree abnf::treep)
  (abnf::make-tree-nonleaf
   :rulename? (abnf::rulename rulename)
   :branches (list (abnf::tree-list-fix children))))

(define parser-symbols-to-nats ((syms true-listp))
  :returns (nats nat-listp)
  (cond ((endp syms) nil)
        ((natp (car syms))
         (cons (car syms) (parser-symbols-to-nats (cdr syms))))
        (t (parser-symbols-to-nats (cdr syms)))))

(define parse-token ((chars stringp) (input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (abnf::parse-schars chars input)
  ///

  (defret len-of-parse-token-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-token-<
    (implies (and (not (reserrp tree))
                  (consp (str::explode chars)))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear))

(define parse-keyword ((chars stringp) (input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :short "Parse a case-sensitive keyword with Futhark's word boundary rule."
  (b* (((mv tree rest-input) (parse-token chars input))
       ((when (reserrp tree)) (mv (reserrf-push tree) rest-input))
       ((when (and (consp rest-input)
                   (ir-word-char-codepointp (car rest-input))))
        (mv (reserrf (list :keyword-boundary (str-fix chars)))
            (nat-list-fix input))))
    (mv tree rest-input))
  ///

  (defret len-of-parse-keyword-<=
    (<= (len rest-input)
        (len input))
    :rule-classes :linear)

  (defret len-of-parse-keyword-<
    (implies (and (not (reserrp tree))
                  (consp (str::explode chars)))
             (< (len rest-input)
                (len input)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable parse-keyword)
             :use (:instance len-of-parse-token-<
                             (chars chars)
                             (input input))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types and parameters.

(defines parse-types

  (define parse-type ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    (b* (;; array-type = "[" ws word ws "]" ws type
         ((mv open input1) (parse-token "[" input))
         ((unless (reserrp open))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((pok word) (parse-word input))
               ((pok ws2) (parse-ws input))
               ((pok close) (parse-token "]" input))
               ((pok ws3) (parse-ws input))
               ((pok elem) (parse-type input))
               (array-tree (make-cst "array-type"
                                     (list open ws1 word ws2 close ws3 elem))))
            (mv (make-cst "type" (list array-tree)) input)))
         ;; prim-type = word
         ((pok word) (parse-word input))
         (prim-tree (make-cst "prim-type" (list word))))
      (mv (make-cst "type" (list prim-tree)) input)))

  (define parse-type-list ((close stringp) (input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 1)
    (b* (((mv close-tree ?close-rest) (parse-token close input))
         ((unless (reserrp close-tree))
          (mv nil (nat-list-fix input)))
         ((pok< type) (parse-type input))
         ((pok ws1) (parse-ws input))
         ((mv comma input1) (parse-token "," input))
         ((when (reserrp comma))
          (mv (list type ws1) input))
         ((pok ws2) (parse-ws input1))
         ((mv trailing-close ?trailing-rest) (parse-token close input))
         ((unless (reserrp trailing-close))
          (mv (reserrf (list :trailing-comma close)) input))
         ((mv rest input) (parse-type-list close input))
         ((when (reserrp rest)) (mv (reserrf-push rest) input)))
      (mv (append (list type ws1 comma ws2) rest) input)))

  :prepwork
  ((defun parse-types-expand-hints (id clause world)
     (declare (ignore id world))
     (cond ((acl2::occur-lst '(acl2::flag-is 'parse-type) clause)
            '(:expand (parse-type input)))
           ((acl2::occur-lst '(acl2::flag-is 'parse-type-list) clause)
            '(:expand (parse-type-list close input))))))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))

  :returns-hints
  (("Goal" :in-theory (disable parse-type parse-type-list))
   parse-types-expand-hints)

  :verify-guards nil

  ///

  (defret-mutual len-of-parse-types
    (defret len-of-parse-type-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-type)
    (defret len-of-parse-type-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-type)
    (defret len-of-parse-type-list-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-type-list)
    :hints (("Goal"
             :in-theory (disable parse-type
                                 parse-type-list))
            parse-types-expand-hints))

  (verify-guards parse-type
    :hints (("Goal"
             :in-theory (disable parse-type
                                 parse-type-list)))))

(define parse-result-types ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< open) (parse-token "{" input))
       ((pok ws1) (parse-ws input))
       ((mv item-trees input) (parse-type-list "}" input))
       ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
       ((pok ws2) (parse-ws input))
       ((pok close) (parse-token "}" input)))
    (mv (make-cst "result-types"
                  (append (list open ws1)
                          (append item-trees (list ws2 close))))
        input))
  ///

  (defret len-of-parse-result-types-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-result-types-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-entry-type ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  :measure (len input)
  :verify-guards nil
  (b* (((mv open input1) (parse-token "[" input))
       ((unless (reserrp open))
        (b* (((unless (mbt (< (len input1) (len input))))
              (mv (reserrf :impossible) input1))
             ((pok ws1) (parse-ws input1))
             ((pok close) (parse-token "]" input))
             ((pok ws2) (parse-ws input))
             ((pok elem) (parse-entry-type input))
             (array-tree (make-cst "entry-array-type"
                                   (list open ws1 close ws2 elem))))
          (mv (make-cst "entry-type" (list array-tree)) input)))
       ((pok word) (parse-word input))
       (prim-tree (make-cst "prim-type" (list word))))
    (mv (make-cst "entry-type" (list prim-tree)) input))
  ///

  (defret len-of-parse-entry-type-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-entry-type-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(verify-guards parse-entry-type
  :hints (("Goal" :in-theory (enable parse-entry-type))))

(define parse-entry-type-list ((close stringp) (input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :measure (len input)
  (b* (((mv close-tree ?close-rest) (parse-token close input))
       ((unless (reserrp close-tree))
        (mv nil (nat-list-fix input)))
       ((pok< type) (parse-entry-type input))
       ((pok ws1) (parse-ws input))
       ((mv comma input1) (parse-token "," input))
       ((when (reserrp comma))
        (mv (list type ws1) input))
       ((pok ws2) (parse-ws input1))
       ((mv trailing-close ?trailing-rest) (parse-token close input))
       ((unless (reserrp trailing-close))
        (mv (reserrf (list :trailing-comma close)) input))
       ((mv rest input) (parse-entry-type-list close input))
       ((when (reserrp rest)) (mv (reserrf-push rest) input)))
    (mv (append (list type ws1 comma ws2) rest) input))
  ///

  (defret len-of-parse-entry-type-list-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))

(define parse-entry-result-type-list ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< open) (parse-token "{" input))
       ((pok ws1) (parse-ws input))
       ((mv item-trees input) (parse-entry-type-list "}" input))
       ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
       ((pok ws2) (parse-ws input))
       ((pok close) (parse-token "}" input)))
    (mv (make-cst "entry-result-type-list"
                  (append (list open ws1)
                          (append item-trees (list ws2 close))))
        input))
  ///

  (defret len-of-parse-entry-result-type-list-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-entry-result-type-list-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-entry-result-types ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((mv result-types rest) (parse-entry-result-type-list input))
       ((unless (reserrp result-types))
        (mv (make-cst "entry-result-types" (list result-types)) rest))
       ((pok< type) (parse-entry-type input)))
    (mv (make-cst "entry-result-types" (list type)) input))
  ///

  (defret len-of-parse-entry-result-types-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-entry-result-types-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-param ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< name) (parse-name input))
       ((pok ws1) (parse-ws input))
       ((pok colon) (parse-token ":" input))
       ((pok ws2) (parse-ws input))
       ((pok type) (parse-type input)))
    (mv (make-cst "param" (list name ws1 colon ws2 type)) input))
  ///

  (defret len-of-parse-param-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-param-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-param-list ((close stringp) (input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :measure (len input)
  (b* (((mv close-tree ?close-rest) (parse-token close input))
       ((unless (reserrp close-tree))
        (mv nil (nat-list-fix input)))
       ((pok< param) (parse-param input))
       ((pok ws1) (parse-ws input))
       ((mv comma input1) (parse-token "," input))
       ((when (reserrp comma))
        (mv (list param ws1) input))
       ((pok ws2) (parse-ws input1))
       ((mv trailing-close ?trailing-rest) (parse-token close input))
       ((unless (reserrp trailing-close))
        (mv (reserrf (list :trailing-comma close)) input))
       ((mv rest input) (parse-param-list close input))
       ((when (reserrp rest)) (mv (reserrf-push rest) input)))
    (mv (append (list param ws1 comma ws2) rest) input))
  ///

  (defret len-of-parse-param-list-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))

(define parse-params ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< open) (parse-token "(" input))
       ((pok ws1) (parse-ws input))
       ((mv item-trees input) (parse-param-list ")" input))
       ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
       ((pok ws2) (parse-ws input))
       ((pok close) (parse-token ")" input)))
    (mv (make-cst "params"
                  (append (list open ws1)
                          (append item-trees (list ws2 close))))
        input))
  ///

  (defret len-of-parse-params-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-params-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-pattern ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< open) (parse-token "{" input))
       ((pok ws1) (parse-ws input))
       ((mv item-trees input) (parse-param-list "}" input))
       ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
       ((pok ws2) (parse-ws input))
       ((pok close) (parse-token "}" input)))
    (mv (make-cst "pattern"
                  (append (list open ws1)
                          (append item-trees (list ws2 close))))
        input))
  ///

  (defret len-of-parse-pattern-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-pattern-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expressions, statements, and bodies.

(define parser-tree-rulename-p ((tree abnf::treep) (rulename stringp))
  :returns (yes/no booleanp)
  (and (abnf::tree-case tree :nonleaf)
       (equal (abnf::tree-nonleaf->rulename? tree)
              (abnf::rulename rulename))))

(defthm tree-kind-when-parser-tree-rulename-p
  (implies (parser-tree-rulename-p tree rulename)
           (equal (abnf::tree-kind tree) :nonleaf))
  :hints (("Goal" :in-theory (enable parser-tree-rulename-p))))

(define exp-cst-kind-p ((tree abnf::treep) (kind stringp))
  :returns (yes/no booleanp)
  (b* (((unless (parser-tree-rulename-p tree "exp")) nil)
       (branches (abnf::tree-nonleaf->branches tree))
       ((unless (and (consp branches)
                     (endp (cdr branches)))) nil)
       (children (car branches))
       ((unless (and (consp children)
                     (endp (cdr children)))) nil))
    (parser-tree-rulename-p (car children) kind)))

(define entry-result-type-list-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  (b* (((unless (parser-tree-rulename-p tree "entry-result-types")) nil)
       (branches (abnf::tree-nonleaf->branches tree))
       ((unless (and (consp branches)
                     (endp (cdr branches)))) nil)
       (children (car branches))
       ((unless (and (consp children)
                     (endp (cdr children)))) nil))
    (parser-tree-rulename-p (car children) "entry-result-type-list")))

(define map-input-children-p ((trees abnf::tree-listp))
  :returns (yes/no booleanp)
  (cond ((endp trees) t)
        ((parser-tree-rulename-p (car trees) "exp")
         (and (exp-cst-kind-p (car trees) "name")
              (map-input-children-p (cdr trees))))
        (t (map-input-children-p (cdr trees)))))

(define map-inputs-cst-p ((tree abnf::treep))
  :returns (yes/no booleanp)
  (b* (((unless (abnf::tree-case tree :nonleaf)) nil)
       (exp-branches (abnf::tree-nonleaf->branches tree))
       ((unless (and (consp exp-branches)
                     (endp (cdr exp-branches)))) nil)
       (exp-children (car exp-branches))
       ((unless (and (consp exp-children)
                     (endp (cdr exp-children)))) nil)
       (brace-tree (car exp-children))
       ((unless (parser-tree-rulename-p brace-tree "brace-exp")) nil)
       (brace-branches (abnf::tree-nonleaf->branches brace-tree))
       ((unless (and (consp brace-branches)
                     (endp (cdr brace-branches)))) nil))
    (map-input-children-p (car brace-branches))))

(defines parse-expressions

  (define parse-exp ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 0)
    (b* (;; lambda-exp
         ((mv lambda input1) (parse-token "\\" input))
         ((unless (reserrp lambda))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((pok pattern) (parse-pattern input))
               ((pok ws2) (parse-ws input))
               ((pok colon) (parse-token ":" input))
               ((pok ws3) (parse-ws input))
               ((pok result-types) (parse-result-types input))
               ((pok ws4) (parse-ws input))
               ((pok arrow) (parse-token "->" input))
               ((pok ws5) (parse-ws input))
               ((pok body) (parse-lambda-body input))
               (tree (make-cst "lambda-exp"
                               (list lambda ws1 pattern ws2 colon ws3
                                     result-types ws4 arrow ws5 body))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; array-exp
         ((mv open-bracket input1) (parse-token "[" input))
         ((unless (reserrp open-bracket))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((mv item-trees input) (parse-exp-list "]" input))
               ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
               ((pok ws2) (parse-ws input))
               ((pok close-bracket) (parse-token "]" input))
               ((pok ws3) (parse-ws input))
               ((pok colon) (parse-token ":" input))
               ((pok ws4) (parse-ws input))
               ((pok row-marker) (parse-token "[]" input))
               ((pok type) (parse-type input))
               (tree (make-cst "array-exp"
                               (append (list open-bracket ws1)
                                       (append item-trees
                                               (list ws2 close-bracket
                                                     ws3 colon ws4 row-marker
                                                     type))))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; brace-exp
         ((mv open-brace input1) (parse-token "{" input))
         ((unless (reserrp open-brace))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((mv item-trees input) (parse-exp-list "}" input))
               ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
               ((pok ws2) (parse-ws input))
               ((pok close-brace) (parse-token "}" input))
               (tree (make-cst "brace-exp"
                               (append (list open-brace ws1)
                                       (append item-trees
                                               (list ws2 close-brace))))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; apply-exp
         ((mv apply input1) (parse-keyword "apply" input))
         ((unless (reserrp apply))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((pok name) (parse-name input))
               ((pok ws2) (parse-ws input))
               ((pok open) (parse-token "(" input))
               ((pok ws3) (parse-ws input))
               ((mv arg-trees input) (parse-exp-list ")" input))
               ((when (reserrp arg-trees)) (mv (reserrf-push arg-trees) input))
               ((pok ws4) (parse-ws input))
               ((pok close) (parse-token ")" input))
               ((pok ws5) (parse-ws input))
               ((pok colon) (parse-token ":" input))
               ((pok ws6) (parse-ws input))
               ((pok result-types) (parse-result-types input))
               (tree (make-cst "apply-exp"
                               (append (list apply ws1 name ws2 open ws3)
                                       (append arg-trees
                                               (list ws4 close ws5 colon
                                                     ws6 result-types))))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; map-exp
         ((mv map input1) (parse-keyword "map" input))
         ((unless (reserrp map))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((pok open) (parse-token "(" input))
               ((pok ws2) (parse-ws input))
               ((pok< width) (parse-exp input))
               ((unless (or (exp-cst-kind-p width "literal")
                            (exp-cst-kind-p width "name")))
                (mv (reserrf :map-width-must-be-a-subexpression) input))
               ((pok ws3) (parse-ws input))
               ((pok comma1) (parse-token "," input))
               ((pok ws4) (parse-ws input))
               ((pok< inputs) (parse-exp input))
               ((unless (map-inputs-cst-p inputs))
                (mv (reserrf :map-inputs-must-be-a-brace-list-of-names) input))
               ((pok ws5) (parse-ws input))
               ((pok comma2) (parse-token "," input))
               ((pok ws6) (parse-ws input))
               ((pok< lambda) (parse-exp input))
               ((unless (exp-cst-kind-p lambda "lambda-exp"))
                (mv (reserrf :map-function-must-be-a-lambda) input))
               ((pok ws7) (parse-ws input))
               ((mv comma3 input1) (parse-token "," input))
               ((when (reserrp comma3))
                (b* (((pok close) (parse-token ")" input))
                     (tree (make-cst
                            "map-exp"
                            (list map ws1 open ws2 width ws3 comma1 ws4
                                  inputs ws5 comma2 ws6 lambda ws7 close))))
                  (mv (make-cst "exp" (list tree)) input)))
               ((pok ws8) (parse-ws input1))
               ((pok< post-lambda) (parse-exp input))
               ((unless (exp-cst-kind-p post-lambda "lambda-exp"))
                (mv (reserrf :map-post-function-must-be-a-lambda) input))
               ((pok ws9) (parse-ws input))
               ((pok close) (parse-token ")" input))
               (tree (make-cst
                      "map-exp"
                      (list map ws1 open ws2 width ws3 comma1 ws4
                            inputs ws5 comma2 ws6 lambda ws7 comma3 ws8
                            post-lambda ws9 close))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; paren-exp
         ((mv open-paren input1) (parse-token "(" input))
         ((unless (reserrp open-paren))
          (b* (((unless (mbt (< (len input1) (len input))))
                (mv (reserrf :impossible) input1))
               ((pok ws1) (parse-ws input1))
               ((pok expr) (parse-exp input))
               ((pok ws2) (parse-ws input))
               ((pok close-paren) (parse-token ")" input))
               (tree (make-cst "paren-exp"
                               (list open-paren ws1 expr ws2 close-paren))))
            (mv (make-cst "exp" (list tree)) input)))
         ;; call-exp or word expression.
         ((pok< name-or-word) (parse-name input))
         (word-rest input)
         ((pok ws1) (parse-ws input))
         ((mv open input1) (parse-token "(" input))
         ((unless (reserrp open))
          (b* (((pok ws2) (parse-ws input1))
               ((mv arg-trees input) (parse-exp-list ")" input))
               ((when (reserrp arg-trees)) (mv (reserrf-push arg-trees) input))
               ((pok ws3) (parse-ws input))
               ((pok close) (parse-token ")" input))
               (call (make-cst "call-exp"
                               (append (list name-or-word ws1 open ws2)
                                       (append arg-trees
                                               (list ws3 close))))))
            (mv (make-cst "exp" (list call)) input)))
         (text (codepoints=>string
                (parser-symbols-to-nats
                 (abnf::tree->string name-or-word))))
         ((when (reserrp text))
          (mv (reserrf-push text) input))
         (word-text text)
         (tree (if (ir-literal-tokenp word-text)
                   (make-cst "literal" (list name-or-word))
                 name-or-word)))
      (mv (make-cst "exp" (list tree)) word-rest)))

  (define parse-exp-list ((close stringp) (input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 1)
    (b* (((mv close-tree ?close-rest) (parse-token close input))
         ((unless (reserrp close-tree))
          (mv nil (nat-list-fix input)))
         ((pok< expr) (parse-exp input))
         ((pok ws1) (parse-ws input))
         ((mv comma input1) (parse-token "," input))
         ((when (reserrp comma))
          (mv (list expr ws1) input))
         ((pok ws2) (parse-ws input1))
         ((mv trailing-close ?trailing-rest) (parse-token close input))
         ((unless (reserrp trailing-close))
          (mv (reserrf (list :trailing-comma close)) input))
         ((mv rest input) (parse-exp-list close input))
         ((when (reserrp rest)) (mv (reserrf-push rest) input)))
      (mv (append (list expr ws1 comma ws2) rest) input)))

  (define parse-result-exps ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 2)
    (b* (((pok< open) (parse-token "{" input))
         ((pok ws1) (parse-ws input))
         ((mv item-trees input) (parse-exp-list "}" input))
         ((when (reserrp item-trees)) (mv (reserrf-push item-trees) input))
         ((pok ws2) (parse-ws input))
         ((pok close) (parse-token "}" input)))
      (mv (make-cst "result-exps"
                    (append (list open ws1)
                            (append item-trees (list ws2 close))))
          input)))

  (define parse-stmt ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 3)
    (b* (((pok< let) (parse-keyword "let" input))
         ((pok ws1) (parse-ws input))
         ((pok pattern) (parse-pattern input))
         ((pok ws2) (parse-ws input))
         ((pok equal) (parse-token "=" input))
         ((pok ws3) (parse-ws input))
         ((pok expr) (parse-exp input)))
      (mv (make-cst "stmt" (list let ws1 pattern ws2 equal ws3 expr))
          input)))

  (define parse-stmts ((input nat-listp))
    :returns (mv (trees abnf::tree-list-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 4)
    (b* (((mv let ?rest) (parse-keyword "let" input))
         ((when (reserrp let))
          (mv nil (nat-list-fix input)))
         ((pok< stmt) (parse-stmt input))
         ((pok ws) (parse-ws input))
         ((mv rest input) (parse-stmts input))
         ((when (reserrp rest)) (mv (reserrf-push rest) input)))
      (mv (append (list stmt ws) rest) input)))

  (define parse-body-core ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 5)
    (b* ((start-input input)
         ((mv stmt-trees input) (parse-stmts input))
         ((when (reserrp stmt-trees)) (mv (reserrf-push stmt-trees) input))
         ((unless (mbt (<= (len input) (len start-input))))
          (mv (reserrf :impossible) input))
         ((pok< in) (parse-keyword "in" input))
         ((pok ws) (parse-ws input))
         ((pok result-exps) (parse-result-exps input)))
      (mv (make-cst "body-core"
                    (append stmt-trees (list in ws result-exps)))
          input)))

  (define parse-lambda-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 6)
    (b* (((mv result-exps rest) (parse-result-exps input))
         ((unless (reserrp result-exps))
          (mv (make-cst "lambda-body" (list result-exps)) rest))
         ((pok body-core) (parse-body-core input)))
      (mv (make-cst "lambda-body" (list body-core)) input)))

  (define parse-body ((input nat-listp))
    :returns (mv (tree abnf::tree-resultp)
                 (rest-input nat-listp))
    :measure (two-nats-measure (len input) 7)
    (b* (((pok< open) (parse-token "{" input))
         ((pok ws1) (parse-ws input))
         ((mv result-exps rest) (parse-result-exps input))
         ((mv inner input)
          (if (reserrp result-exps)
              (parse-body-core input)
            (mv result-exps rest)))
         ((when (reserrp inner)) (mv (reserrf-push inner) input))
         ((pok ws2) (parse-ws input))
         ((pok close) (parse-token "}" input)))
      (mv (make-cst "body" (list open ws1 inner ws2 close)) input)))

  :prepwork
  ((defun parse-expressions-expand-hints (id clause world)
     (declare (ignore id world))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'parse-exp) clause)
       '(:expand (parse-exp input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-exp-list) clause)
       '(:expand (parse-exp-list close input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-result-exps) clause)
       '(:expand (parse-result-exps input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-stmt) clause)
       '(:expand (parse-stmt input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-stmts) clause)
       '(:expand (parse-stmts input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-body-core) clause)
       '(:expand (parse-body-core input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-lambda-body) clause)
       '(:expand (parse-lambda-body input)))
      ((acl2::occur-lst '(acl2::flag-is 'parse-body) clause)
       '(:expand (parse-body input))))))

  :hints (("Goal" :in-theory (enable nfix o< o-finp two-nats-measure)))

  :returns-hints
  (("Goal"
    :in-theory (disable parse-exp
                        parse-exp-list
                        parse-result-exps
                        parse-stmt
                        parse-stmts
                        parse-body-core
                        parse-lambda-body
                        parse-body))
   parse-expressions-expand-hints)

  :ruler-extenders :all

  :verify-guards nil

  ///

  (defret-mutual len-of-parse-expressions
    (defret len-of-parse-exp-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-exp)
    (defret len-of-parse-exp-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-exp)
    (defret len-of-parse-exp-list-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-exp-list)
    (defret len-of-parse-result-exps-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-result-exps)
    (defret len-of-parse-result-exps-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-result-exps)
    (defret len-of-parse-stmt-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-stmt)
    (defret len-of-parse-stmt-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-stmt)
    (defret len-of-parse-stmts-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-stmts)
    (defret len-of-parse-body-core-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-body-core)
    (defret len-of-parse-body-core-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-body-core)
    (defret len-of-parse-lambda-body-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-lambda-body)
    (defret len-of-parse-lambda-body-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-lambda-body)
    (defret len-of-parse-body-<=
      (<= (len rest-input) (len input))
      :rule-classes :linear
      :fn parse-body)
    (defret len-of-parse-body-<
      (implies (not (reserrp tree))
               (< (len rest-input) (len input)))
      :rule-classes :linear
      :fn parse-body)
    :hints (("Goal"
             :in-theory (disable parse-exp
                                 parse-exp-list
                                 parse-result-exps
                                 parse-stmt
                                 parse-stmts
                                 parse-body-core
                                 parse-lambda-body
                                 parse-body))
            parse-expressions-expand-hints))

  (verify-guards parse-exp
    :hints (("Goal"
             :in-theory (disable parse-exp
                                 parse-exp-list
                                 parse-result-exps
                                 parse-stmt
                                 parse-stmts
                                 parse-body-core
                                 parse-lambda-body
                                 parse-body)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Declarations and programs.

(define parse-entry-attr ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok< entry) (parse-keyword "entry" input))
       ((pok ws1) (parse-ws input))
       ((pok open) (parse-token "(" input))
       ((pok ws2) (parse-ws input))
       ((pok string-lit) (parse-string-lit input))
       ((pok ws3) (parse-ws input))
       ((pok comma1) (parse-token "," input))
       ((pok ws4) (parse-ws input))
       ((pok entry-input-types) (parse-pattern input))
       ((pok ws5) (parse-ws input))
       ((pok comma2) (parse-token "," input))
       ((pok ws6) (parse-ws input))
       ((pok entry-result-types) (parse-entry-result-types input))
       ((pok ws7) (parse-ws input))
       ((mv comma3 input1) (parse-token "," input))
       ((when (reserrp comma3))
        (b* (((pok close) (parse-token ")" input)))
          (mv (make-cst "entry-attr"
                        (list entry ws1 open ws2 string-lit ws3 comma1 ws4
                              entry-input-types ws5 comma2 ws6
                              entry-result-types ws7 close))
              input)))
       ((when (entry-result-type-list-cst-p entry-result-types))
        (mv (reserrf :entry-doc-not-supported-with-legacy-result-types)
            input))
       ((pok ws8) (parse-ws input1))
       ((pok doc-string) (parse-string-lit input))
       (entry-doc (make-cst "entry-doc" (list doc-string)))
       ((pok ws9) (parse-ws input))
       ((pok close) (parse-token ")" input)))
    (mv (make-cst "entry-attr"
                  (list entry ws1 open ws2 string-lit ws3 comma1 ws4
                        entry-input-types ws5 comma2 ws6
                        entry-result-types ws7 comma3 ws8 entry-doc ws9 close))
        input))
  ///

  (defret len-of-parse-entry-attr-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-entry-attr-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-decl ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (;; fun-decl
       ((mv fun input1) (parse-keyword "fun" input))
       ((unless (reserrp fun))
        (b* (((unless (mbt (< (len input1) (len input))))
              (mv (reserrf :impossible) input1))
             ((pok ws1) (parse-ws input1))
             ((pok name) (parse-name input))
             ((pok ws2) (parse-ws input))
             ((pok params) (parse-params input))
             ((pok ws3) (parse-ws input))
             ((pok colon) (parse-token ":" input))
             ((pok ws4) (parse-ws input))
             ((pok result-types) (parse-result-types input))
             ((pok ws5) (parse-ws input))
             ((pok equal) (parse-token "=" input))
             ((pok ws6) (parse-ws input))
             ((pok body) (parse-body input))
             (fun-tree (make-cst "fun-decl"
                                 (list fun ws1 name ws2 params ws3 colon
                                       ws4 result-types ws5 equal ws6 body))))
          (mv (make-cst "decl" (list fun-tree)) input)))
       ;; entry-decl
       ((pok< entry-attr) (parse-entry-attr input))
       ((pok ws1) (parse-ws input))
       ((pok name) (parse-name input))
       ((pok ws2) (parse-ws input))
       ((pok params) (parse-params input))
       ((pok ws3) (parse-ws input))
       ((pok colon) (parse-token ":" input))
       ((pok ws4) (parse-ws input))
       ((pok result-types) (parse-result-types input))
       ((pok ws5) (parse-ws input))
       ((pok equal) (parse-token "=" input))
       ((pok ws6) (parse-ws input))
       ((pok body) (parse-body input))
       (entry-tree (make-cst "entry-decl"
                             (list entry-attr ws1 name ws2 params ws3 colon
                                   ws4 result-types ws5 equal ws6 body))))
    (mv (make-cst "decl" (list entry-tree)) input))
  ///

  (defret len-of-parse-decl-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear)

  (defret len-of-parse-decl-<
    (implies (not (reserrp tree))
             (< (len rest-input) (len input)))
    :rule-classes :linear))

(define parse-decls ((input nat-listp))
  :returns (mv (trees abnf::tree-list-resultp)
               (rest-input nat-listp))
  :measure (len input)
  (b* ((start-input input)
       ((mv decl rest) (parse-decl input))
       ((when (reserrp decl))
        (mv nil (nat-list-fix input)))
       ((pok ws) (parse-ws rest))
       ((unless (mbt (< (len input) (len start-input))))
        (mv (reserrf :impossible) input))
       ((mv rest-trees input) (parse-decls input))
       ((when (reserrp rest-trees)) (mv (reserrf-push rest-trees) input)))
    (mv (append (list decl ws) rest-trees) input))
  ///

  (defret len-of-parse-decls-<=
    (<= (len rest-input) (len input))
    :rule-classes :linear))

(define parse-name-source ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok kw) (parse-keyword "name_source" input))
       ((pok ws1) (parse-ws input))
       ((pok open) (parse-token "{" input))
       ((pok ws2) (parse-ws input))
       ((pok word) (parse-word input))
       ((pok ws3) (parse-ws input))
       ((pok close) (parse-token "}" input)))
    (mv (make-cst "name-source"
                  (list kw ws1 open ws2 word ws3 close))
        input)))

(define parse-types-section ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok kw) (parse-keyword "types" input))
       ((pok ws1) (parse-ws input))
       ((pok open) (parse-token "{" input))
       ((pok ws2) (parse-ws input))
       ((pok close) (parse-token "}" input)))
    (mv (make-cst "types-section"
                  (list kw ws1 open ws2 close))
        input)))

(define parse-optional-name-source ((input nat-listp))
  :returns (mv (tree? abnf::tree-optionp)
               (rest-input nat-listp))
  (b* (((mv tree rest) (parse-name-source input)))
    (if (reserrp tree)
        (mv nil (nat-list-fix input))
      (mv tree rest))))

(define parse-optional-types-section ((input nat-listp))
  :returns (mv (tree? abnf::tree-optionp)
               (rest-input nat-listp))
  (b* (((mv tree rest) (parse-types-section input)))
    (if (reserrp tree)
        (mv nil (nat-list-fix input))
      (mv tree rest))))

(define parse-program ((input nat-listp))
  :returns (mv (tree abnf::tree-resultp)
               (rest-input nat-listp))
  (b* (((pok ws1) (parse-ws input))
       ((mv name-source input) (parse-optional-name-source input))
       ((pok ws2) (parse-ws input))
       ((mv types-section input) (parse-optional-types-section input))
       ((pok ws3) (parse-ws input))
       ((mv decls input) (parse-decls input))
       ((when (reserrp decls)) (mv (reserrf-push decls) input))
       (children (append (list ws1)
                         (append (if name-source
                                     (list name-source ws2)
                                   (list ws2))
                                 (append (if types-section
                                             (list types-section ws3)
                                           (list ws3))
                                         decls)))))
    (mv (make-cst "program" children) input)))
