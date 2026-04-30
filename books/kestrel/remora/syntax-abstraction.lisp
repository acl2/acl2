; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "parser")
(include-book "abstract-syntax")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/nat-natlist-result" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)
(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "projects/abnf/tree-utilities" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    abnf::tree-listp-when-result-not-error
                    abnf::tree-list-listp-when-result-not-error
                    abnf::tree-list-tuple2p-when-result-not-error
                    abnf::tree-list-tuple3p-when-result-not-error
                    abnf::tree-list-tuple5p-when-result-not-error
                    abnf::tree-list-tuple6p-when-result-not-error
                    abnf::tree-list-tuple8p-when-result-not-error
                    acl2::natp-when-result-not-error
                    acl2::nat-listp-when-result-not-error
                    acl2::reserrp-when-nat-resultp-not-ok
                    acl2::stringp-when-result-not-error
                    dimp-when-result-not-error
                    dim-listp-when-result-not-error
                    shapep-when-result-not-error
                    shape-listp-when-result-not-error
                    ispacep-when-result-not-error
                    ispace-listp-when-result-not-error
                    ispace-varp-when-result-not-error
                    ispace-var-listp-when-result-not-error
                    type-varp-when-result-not-error
                    type-var-listp-when-result-not-error
                    typep-when-result-not-error
                    type-listp-when-result-not-error
                    base-typep-when-result-not-error
                    base-valuep-when-result-not-error
                    sign-optionp-when-result-not-error
                    dec-digit-char-listp-when-result-not-error
                    str::dec-digit-char-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-abstraction
  :parents (abstract-syntax)
  :short "Mapping from concrete to abstract syntax, for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " is an abstraction of the concrete syntax described by "
    (xdoc::seetopic "grammar" "the ABNF grammar")
    ".  Here we define the abstraction mapping from
     CSTs (concrete syntax trees) produced by "
    (xdoc::seetopic "parser" "the parser")
    " to ASTs (abstract syntax trees) defined as "
    (xdoc::seetopic "abstract-syntax-trees" "fixtypes")
    ".")
   (xdoc::p
    "This is the first slice of the abstraction: it covers identifiers,
     decimals, base values, base types, type variables, ispace variables,
     and the @('dim')/@('shape')/@('ispace') cluster.  Types and expressions
     remain to be added."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; leaves and atomic forms
;;
;; Result types for AST nodes (e.g. dim-result, shape-result, ispace-result)
;; come from abstract-syntax-derived-fixtypes.lisp, included via abstract-syntax.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-nats-to-string ((nats nat-listp))
  :returns (str acl2::string-resultp)
  :short "Convert a list of Unicode code points to an ACL2 string,
          UTF-8-encoded."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 strings are sequences of bytes (char codes 0-255), so a
     single non-ASCII code point such as U+03B1 cannot fit in one
     character.  Instead we UTF-8-encode the code points back into
     bytes and pack those bytes into the ACL2 string.  This is
     symmetric to the bytes-to-code-points decoding done by "
    (xdoc::seetopic "post-parsing" "@('parse-program-from-bytes')")
    ".")
   (xdoc::p
    "Consequence: for ASCII inputs, the resulting ACL2 string holds
     one byte per code point (no change from the natural encoding).
     For non-ASCII inputs, the string holds the UTF-8 byte sequence,
     so @('(length name)') is the byte count rather than the
     code-point count.  Two strings produced from the same source
     identifier compare @(see equal), so this is fine for use as a
     variable-name representation; consumers that need code points
     back can decode with @('acl2::utf8=>ustring').")
   (xdoc::p
    "The error case @(':invalid-codepoints') is structural &mdash;
     it occurs only if @('nats') contains values outside the
     Unicode scalar range (i.e. surrogates U+D800-DFFF, or values
     above U+10FFFF).  Code-point lists produced by the Remora
     parser cannot contain such values, because the grammar's
     terminal ranges already exclude them; the check is purely
     defensive."))
  (b* ((nats (acl2::nat-list-fix nats)))
    (if (acl2::ustring? nats)
        (acl2::nats=>string (acl2::ustring=>utf8 nats))
      (reserrf (list :invalid-codepoints nats))))
  ///
  (defret stringp-of-abs-nats-to-string
    (implies (not (reserrp str))
             (stringp str))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-digit-to-nat ((tree abnf::treep))
  :returns (nat acl2::nat-resultp :hints (("Goal" :in-theory (enable natp))))
  :short "Abstract a @('digit') to a natural number."
  (b* (((okf nat) (abnf::check-tree-nonleaf-num-range tree "digit" #x30 #x39)))
    (- nat #x30))
  ///
  (defret natp-of-abs-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable natp))))
  (defret abs-digit-to-nat-bound
    (implies (not (reserrp nat))
             (< nat 10))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-digit-to-nat-aux ((trees abnf::tree-listp) (acc natp))
  :returns (nat acl2::nat-resultp)
  :parents (abs-decimal)
  :short "Big-endian accumulation of a digit list."
  (b* (((when (endp trees)) (lnfix acc))
       ((okf d) (abs-digit-to-nat (car trees))))
    (abs-*-digit-to-nat-aux (cdr trees)
                            (+ d (* (lnfix acc) 10))))
  ///
  (defret natp-of-abs-*-digit-to-nat-aux
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining
    :hints (("Goal" :induct t))))

(define abs-decimal ((tree abnf::treep))
  :returns (nat acl2::nat-resultp)
  :short "Abstract a @('decimal') to a natural number."
  (b* (((okf trees) (abnf::check-tree-nonleaf-1 tree "decimal"))
       ((unless (consp trees))
        (reserrf (list :empty-decimal (abnf::tree-info-for-error tree)))))
    (abs-*-digit-to-nat-aux trees 0))
  ///
  (defret natp-of-abs-decimal
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-ws-decimal ((tree abnf::treep))
  :returns (n acl2::nat-resultp)
  :short "Abstract a @('( ws decimal )') wrapper to a natural number."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf decimal-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-decimal decimal-tree)))

(define abs-*-ws-decimal ((trees abnf::tree-listp))
  :returns (nats acl2::nat-list-resultp)
  :short "Abstract @('*( ws decimal )') to a list of natural numbers."
  (b* (((when (endp trees)) nil)
       ((okf n) (abs-ws-decimal (car trees)))
       ((okf rest) (abs-*-ws-decimal (cdr trees))))
    (cons n rest)))

(define abs-shape-lit ((tree abnf::treep))
  :returns (nats acl2::nat-list-resultp)
  :short "Abstract a @('shape-lit') to a list of natural numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is @('shape-lit = \"[\" *( ws decimal ) ws \"]\"').
     This is the concrete shape literal used inside @('array-exp')
     and @('frame-exp'); it produces a flat list of dimensions
     (natural numbers).  Note that this differs from the bracketed
     shape form in the @('shape') rule, which contains arbitrary
     ispaces."))
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "shape-lit")))
    (abs-*-ws-decimal sub.2nd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-symbols-to-nats ((syms true-listp))
  :returns (nats nat-listp)
  :short "Convert an @(tsee abnf::stringp) (list of nats and rule symbols)
          to a @(tsee nat-list), discarding any non-nat entries."
  (cond ((endp syms) nil)
        ((natp (car syms))
         (cons (car syms) (abs-symbols-to-nats (cdr syms))))
        (t (abs-symbols-to-nats (cdr syms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-identifier ((tree abnf::treep))
  :returns (str acl2::string-resultp)
  :short "Abstract an @('identifier') to an ACL2 string."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar's @('identifier') rule allows arbitrary non-disallowed
     Unicode characters.  We collect the leaf code points via
     @(tsee abnf::tree->string), discarding any non-nat entries
     (which correspond to @(':leafrule') leaves and do not appear
     in our parser's output)."))
  (b* (((okf &) (abnf::check-tree-nonleaf tree "identifier"))
       (raw (abnf::tree->string tree))
       (nats (abs-symbols-to-nats raw)))
    (abs-nats-to-string nats))
  ///
  (defret stringp-of-abs-identifier
    (implies (not (reserrp str))
             (stringp str))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-bool-val ((tree abnf::treep))
  :returns (b acl2::boolean-resultp)
  :short "Abstract a @('bool-val') to an ACL2 boolean."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "bool-val"))
       (true-pass (abnf::check-tree-ichars inner "#t"))
       ((unless (reserrp true-pass)) t)
       (false-pass (abnf::check-tree-ichars inner "#f"))
       ((unless (reserrp false-pass)) nil))
    (reserrf (list :found-subtree (abnf::tree-info-for-error inner))))
  ///
  (defret booleanp-of-abs-bool-val
    (implies (not (reserrp b))
             (booleanp b))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-num-val ((tree abnf::treep))
  :returns (val base-value-resultp)
  :short "Abstract a @('num-val') to a @(tsee base-value).
          Currently handles only integers; @('float-lit') produces an error."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is
     @({
       num-val = [ \"+\" / \"-\" ] ( float-lit / decimal )
     })
     The CST has two tree-lists: an optional sign and a wrapper around
     either @('float-lit') or @('decimal').  We descend into the second
     wrapper, attempt @('decimal') first, and emit a not-yet-implemented
     error if a @('float-lit') is encountered.")
   (xdoc::p
    "For the @('decimal') case we build an @(tsee int-lit) that
     preserves the source-level sign (absent vs.@ explicit @('+') vs.@
     @('-')) and the decimal digits (including any leading zeros).  The
     numeric value is recovered later by the static/dynamic semantics."))
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "num-val"))
       ;; First tree-list: optional sign wrapper (single tree).
       ((okf sign-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf sign?) (abs-optional-sign-to-option sign-tree))
       ;; Second tree-list: the inner decimal-or-float-lit wrapper.
       ((okf body-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf body-treess) (abnf::check-tree-nonleaf body-tree nil))
       ((okf body-trees) (abnf::check-tree-list-list-1 body-treess))
       ((okf inner) (abnf::check-tree-list-1 body-trees))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "decimal")
           (b* (((okf digits) (abs-decimal-to-digits inner))
                ;; abs-decimal-to-digits already ensures consp, but the
                ;; check below makes int-lit's :require visible to the
                ;; guard verifier.
                ((unless (consp digits))
                 (reserrf :empty-decimal-digits-impossible)))
             (make-base-value-int :lit (make-int-lit :sign? sign?
                                                     :digits digits))))
          ((equal rulename? "float-lit")
           (reserrf (list :float-lit-not-yet-implemented
                          (abnf::tree-info-for-error inner))))
          (t (reserrf (list :unexpected-num-val-body
                            (abnf::tree-info-for-error inner))))))

  :prepwork
  ((define abs-optional-sign-to-option ((tree abnf::treep))
     :returns (s? sign-option-resultp)
     :parents nil
     :short "Abstract @('[ \"+\" / \"-\" ]') to a @(tsee sign-option)."
     (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
          ((when (endp treess)) (sign-option-none))
          ((okf trees) (abnf::check-tree-list-list-1 treess))
          ((okf inner) (abnf::check-tree-list-1 trees))
          (plus-pass (abnf::check-tree-ichars inner "+"))
          ((unless (reserrp plus-pass))
           (sign-option-some (sign-plus)))
          (minus-pass (abnf::check-tree-ichars inner "-"))
          ((unless (reserrp minus-pass))
           (sign-option-some (sign-minus))))
       (reserrf (list :unexpected-sign (abnf::tree-info-for-error inner)))))

   (define abs-*-digit-tree-to-char ((trees abnf::tree-listp))
     :returns (chars dec-digit-char-list-resultp)
     :parents nil
     :short "Abstract a list of @('digit') trees to a list of
             @(see str::dec-digit-char)s, preserving leading zeros."
     (b* (((when (endp trees)) nil)
          ((okf inner)
           (abnf::check-tree-nonleaf-1-1 (car trees) "digit"))
          ((okf leaf) (abnf::check-tree-leafterm inner))
          ((unless (consp leaf))
           (reserrf (list :empty-digit-leaf
                          (abnf::tree-info-for-error inner))))
          (nat (car leaf))
          ((unless (and (<= #x30 nat) (<= nat #x39)))
           (reserrf (list :digit-out-of-range nat)))
          (c (code-char nat))
          ((okf rest) (abs-*-digit-tree-to-char (cdr trees))))
       (cons c rest)))

   (define abs-decimal-to-digits ((tree abnf::treep))
     :returns (digits dec-digit-char-list-resultp)
     :parents nil
     :short "Abstract a @('decimal') to a list of @(see str::dec-digit-char)s,
             preserving leading zeros."
     (b* (((okf trees) (abnf::check-tree-nonleaf-1 tree "decimal"))
          ((unless (consp trees))
           (reserrf (list :empty-decimal (abnf::tree-info-for-error tree)))))
       (abs-*-digit-tree-to-char trees)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-base-val ((tree abnf::treep))
  :returns (val base-value-resultp)
  :short "Abstract a @('base-val') to a @(tsee base-value)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "base-val"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "bool-val")
           (b* (((okf b) (abs-bool-val inner)))
             (make-base-value-bool :value b)))
          ((equal rulename? "num-val")
           (abs-num-val inner))
          (t (reserrf (list :unexpected-base-val-body
                            (abnf::tree-info-for-error inner)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-base-type ((tree abnf::treep))
  :returns (bt base-type-resultp)
  :short "Abstract a @('base-type') to a @(tsee base-type)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "base-type"))
       (bool-pass (abnf::check-tree-ichars inner "Bool"))
       ((unless (reserrp bool-pass)) (make-base-type-bool))
       (int-pass (abnf::check-tree-ichars inner "Int"))
       ((unless (reserrp int-pass)) (make-base-type-int))
       (float-pass (abnf::check-tree-ichars inner "Float"))
       ((unless (reserrp float-pass)) (make-base-type-float)))
    (reserrf (list :unexpected-base-type (abnf::tree-info-for-error inner)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-type-var ((tree abnf::treep))
  :returns (tv type-var-resultp)
  :short "Abstract a @('type-var') to a @(tsee type-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is @('type-var = \"&\" identifier / \"*\" identifier').
     The CST has two tree-lists: the sigil and the identifier.
     The sigil distinguishes the alternatives:
     @('&') for the atom-kinded variant, @('*') for the array-kinded variant."))
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "type-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (atom-pass (abnf::check-tree-ichars sigil-tree "&"))
       ((unless (reserrp atom-pass))
        (b* (((okf name) (abs-identifier id-tree)))
          (make-type-var-atom :name name)))
       (array-pass (abnf::check-tree-ichars sigil-tree "*"))
       ((unless (reserrp array-pass))
        (b* (((okf name) (abs-identifier id-tree)))
          (make-type-var-array :name name))))
    (reserrf (list :type-var-sigil
                   (abnf::tree-info-for-error sigil-tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-ispace-var ((tree abnf::treep))
  :returns (iv ispace-var-resultp)
  :short "Abstract an @('ispace-var') to an @(tsee ispace-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is
     @('ispace-var = \"$\" identifier / \"@\" identifier').
     @('$') introduces a dimension variable;
     @('@') introduces a shape variable."))
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "ispace-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (dim-pass (abnf::check-tree-ichars sigil-tree "$"))
       ((unless (reserrp dim-pass))
        (b* (((okf name) (abs-identifier id-tree)))
          (make-ispace-var-dim :name name)))
       (shape-pass (abnf::check-tree-ichars sigil-tree "@"))
       ((unless (reserrp shape-pass))
        (b* (((okf name) (abs-identifier id-tree)))
          (make-ispace-var-shape :name name))))
    (reserrf (list :ispace-var-sigil
                   (abnf::tree-info-for-error sigil-tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; dim / shape / ispace cluster
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-ispaces

  ;; dim has three alternatives, distinguished by the number of tree-lists
  ;; in its branches:
  ;;   1 -> decimal
  ;;   2 -> "$" identifier
  ;;   5 -> "(" ws dim-arith ws ")"
  (define abs-dim ((tree abnf::treep))
    :returns (d dim-resultp)
    :short "Abstract a @('dim') to a @(tsee dim)."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "dim")))
      (case (len treess)
        (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "dim"))
                ((okf nat) (abs-decimal inner)))
             (make-dim-const :value nat)))
        (2 (b* (((okf (abnf::tree-list-tuple2 sub))
                 (abnf::check-tree-list-list-2 treess))
                ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
                ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
                (dollar-pass (abnf::check-tree-ichars sigil-tree "$"))
                ((when (reserrp dollar-pass))
                 (reserrf (list :dim-sigil
                                (abnf::tree-info-for-error sigil-tree))))
                ((okf name) (abs-identifier id-tree)))
             (make-dim-var :name name)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf da-tree) (abnf::check-tree-list-1 sub.3rd)))
             (abs-dim-arith da-tree)))
        (otherwise
         (reserrf (list :dim-shape (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  ;; dim-arith has branches with 2 tree-lists: an operator and the
  ;; *( ws dim ) repetition.  We currently only support "+"; "*" and "-"
  ;; produce a not-yet-implemented error because the AST has no dim-mul
  ;; or dim-sub constructors yet.
  (define abs-dim-arith ((tree abnf::treep))
    :returns (d dim-resultp)
    :short "Abstract a @('dim-arith') to a @(tsee dim)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree "dim-arith"))
         ((okf op-tree) (abnf::check-tree-list-1 sub.1st))
         (plus-pass (abnf::check-tree-ichars op-tree "+"))
         ((when (reserrp plus-pass))
          (reserrf (list :dim-arith-op-not-yet-implemented
                         (abnf::tree-info-for-error op-tree))))
         ((okf dims) (abs-*-ws-dim sub.2nd)))
      (make-dim-add :dims dims))
    :measure (abnf::tree-count tree))

  ;; ( ws dim ) wrapper: anonymous nonleaf with 2 tree-lists (ws and dim).
  (define abs-ws-dim ((tree abnf::treep))
    :returns (d dim-resultp)
    :short "Abstract a @('( ws dim )') wrapper to a @(tsee dim)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf dim-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-dim dim-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-dim ((trees abnf::tree-listp))
    :returns (ds dim-list-resultp)
    :short "Abstract @('*( ws dim )') to a list of dims."
    (b* (((when (endp trees)) nil)
         ((okf d) (abs-ws-dim (car trees)))
         ((okf rest) (abs-*-ws-dim (cdr trees))))
      (cons d rest))
    :measure (abnf::tree-list-count trees))

  ;; shape has four alternatives:
  ;;   1 -> dim
  ;;   2 -> "@" identifier
  ;;   5 -> "(" ws shape-paren ws ")"
  ;;   5 (different form) -> "[" ws *( ws ispace ) ws "]"
  ;; The last case has 5 tree-lists too, but the third tree-list is the
  ;; *( ws ispace ) repetition list rather than a single tree.  We
  ;; distinguish it by checking whether sub.3rd has length 1 (paren) or
  ;; could be any length including 0 (bracket).  In practice, we try the
  ;; "shape-paren" interpretation first; if the third subtree is not a
  ;; shape-paren rule, we fall through to the bracket interpretation.
  (define abs-shape ((tree abnf::treep))
    :returns (s shape-resultp)
    :short "Abstract a @('shape') to a @(tsee shape)."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "shape")))
      (case (len treess)
        (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "shape"))
                ((okf d) (abs-dim inner)))
             (make-shape-dim :dim d)))
        (2 (b* (((okf (abnf::tree-list-tuple2 sub))
                 (abnf::check-tree-list-list-2 treess))
                ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
                ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
                (at-pass (abnf::check-tree-ichars sigil-tree "@"))
                ((when (reserrp at-pass))
                 (reserrf (list :shape-sigil
                                (abnf::tree-info-for-error sigil-tree))))
                ((okf name) (abs-identifier id-tree)))
             (make-shape-var :name name)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf open-tree) (abnf::check-tree-list-1 sub.1st))
                (lparen-pass (abnf::check-tree-ichars open-tree "("))
                ((unless (reserrp lparen-pass))
                 ;; "(" ws shape-paren ws ")" form
                 (b* (((okf sp-tree) (abnf::check-tree-list-1 sub.3rd)))
                   (abs-shape-paren sp-tree)))
                (lbracket-pass (abnf::check-tree-ichars open-tree "["))
                ((when (reserrp lbracket-pass))
                 (reserrf (list :shape-open
                                (abnf::tree-info-for-error open-tree))))
                ;; "[" ws *( ws ispace ) ws "]" form: sub.3rd is the
                ;; repetition list (a tree-listp).
                ((okf ispaces) (abs-*-ws-ispace sub.3rd))
                (shapes (ispaces-to-shapes ispaces)))
             (make-shape-splice :shapes shapes)))
        (otherwise
         (reserrf (list :shape-shape (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  ;; shape-paren has 2 tree-lists: keyword and the repetition.
  (define abs-shape-paren ((tree abnf::treep))
    :returns (s shape-resultp)
    :short "Abstract a @('shape-paren') to a @(tsee shape)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree "shape-paren"))
         ((okf kw-tree) (abnf::check-tree-list-1 sub.1st))
         (dims-pass (abnf::check-tree-ichars kw-tree "dims"))
         ((unless (reserrp dims-pass))
          (b* (((okf ds) (abs-*-ws-dim sub.2nd)))
            (make-shape-dims :dims ds)))
         (concat-pass (abnf::check-tree-ichars kw-tree "++"))
         ((unless (reserrp concat-pass))
          (b* (((okf ss) (abs-*-ws-shape sub.2nd)))
            (make-shape-append :shapes ss))))
      (reserrf (list :shape-paren-keyword
                     (abnf::tree-info-for-error kw-tree))))
    :measure (abnf::tree-count tree))

  ;; ( ws shape ) wrapper.
  (define abs-ws-shape ((tree abnf::treep))
    :returns (s shape-resultp)
    :short "Abstract a @('( ws shape )') wrapper to a @(tsee shape)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf shape-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-shape shape-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-shape ((trees abnf::tree-listp))
    :returns (ss shape-list-resultp)
    :short "Abstract @('*( ws shape )') to a list of shapes."
    (b* (((when (endp trees)) nil)
         ((okf s) (abs-ws-shape (car trees)))
         ((okf rest) (abs-*-ws-shape (cdr trees))))
      (cons s rest))
    :measure (abnf::tree-list-count trees))

  ;; ispace has 1 tree-list with 1 tree (the dim or shape sub-tree).
  (define abs-ispace ((tree abnf::treep))
    :returns (i ispace-resultp)
    :short "Abstract an @('ispace') to an @(tsee ispace)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "ispace"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "dim")
             (b* (((okf d) (abs-dim inner)))
               (make-ispace-dim :dim d)))
            ((equal rulename? "shape")
             (b* (((okf s) (abs-shape inner)))
               (make-ispace-shape :shape s)))
            (t (reserrf (list :unexpected-ispace-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; ( ws ispace ) wrapper.
  (define abs-ws-ispace ((tree abnf::treep))
    :returns (i ispace-resultp)
    :short "Abstract a @('( ws ispace )') wrapper to an @(tsee ispace)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf ispace-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-ispace ispace-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-ispace ((trees abnf::tree-listp))
    :returns (is ispace-list-resultp)
    :short "Abstract @('*( ws ispace )') to a list of ispaces."
    (b* (((when (endp trees)) nil)
         ((okf i) (abs-ws-ispace (car trees)))
         ((okf rest) (abs-*-ws-ispace (cdr trees))))
      (cons i rest))
    :measure (abnf::tree-list-count trees))

  :ruler-extenders :all
  :verify-guards nil ; done below

  :prepwork
  ((define ispace-to-shape ((i ispacep))
     :returns (s shapep)
     :parents nil
     :short "Lift one ispace to a shape (a dim becomes a singleton shape)."
     (ispace-case i
                  :dim (make-shape-dim :dim i.dim)
                  :shape i.shape))
   (define ispaces-to-shapes ((ispaces ispace-listp))
     :returns (ss shape-listp)
     :parents nil
     :short "Lift each ispace to a shape."
     (cond ((endp ispaces) nil)
           (t (cons (ispace-to-shape (car ispaces))
                    (ispaces-to-shapes (cdr ispaces)))))))

  ///

  (verify-guards abs-ispace)

  (fty::deffixequiv-mutual abs-ispaces))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; type-var / ispace-var list helpers (used by forall/pi/sigma/types)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-ws-type-var ((tree abnf::treep))
  :returns (tv type-var-resultp)
  :short "Abstract a @('( ws type-var )') wrapper to a @(tsee type-var)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf tv-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-type-var tv-tree)))

(define abs-*-ws-type-var ((trees abnf::tree-listp))
  :returns (tvs type-var-list-resultp)
  :short "Abstract @('*( ws type-var )') to a list of @(tsee type-var)s."
  (b* (((when (endp trees)) nil)
       ((okf tv) (abs-ws-type-var (car trees)))
       ((okf rest) (abs-*-ws-type-var (cdr trees))))
    (cons tv rest)))

(define abs-ws-ispace-var ((tree abnf::treep))
  :returns (iv ispace-var-resultp)
  :short "Abstract a @('( ws ispace-var )') wrapper to an @(tsee ispace-var)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf iv-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-ispace-var iv-tree)))

(define abs-*-ws-ispace-var ((trees abnf::tree-listp))
  :returns (ivs ispace-var-list-resultp)
  :short "Abstract @('*( ws ispace-var )') to a list of @(tsee ispace-var)s."
  (b* (((when (endp trees)) nil)
       ((okf iv) (abs-ws-ispace-var (car trees)))
       ((okf rest) (abs-*-ws-ispace-var (cdr trees))))
    (cons iv rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; non-recursive type-variable rules
;;
;; The grammar has separate rules @('atom-type-var') and @('array-type-var')
;; that occur as alternatives of @('type-exp').  These are abstracted directly
;; to a @(tsee type) @(':var') containing a @(tsee type-var) of the matching
;; kind.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-atom-type-var ((tree abnf::treep))
  :returns (ty type-resultp)
  :short "Abstract an @('atom-type-var') to a @(tsee type) @(':var')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "atom-type-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "&"))
       ((when (reserrp sigil-pass))
        (reserrf (list :atom-type-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-type-var :var (make-type-var-atom :name name))))

(define abs-array-type-var ((tree abnf::treep))
  :returns (ty type-resultp)
  :short "Abstract an @('array-type-var') to a @(tsee type) @(':var')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "array-type-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "*"))
       ((when (reserrp sigil-pass))
        (reserrf (list :array-type-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-type-var :var (make-type-var-array :name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; types cluster
;;
;; Following the standard ABNF-parser convention used in PFCS, Aleo Leo,
;; etc., each named rule's CST has one tree-list per ABNF concatenation
;; element.  So @('arrow-type') (8 elements) has 8 tree-lists, etc.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-types

  (define abs-type-exp ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('type-exp') to a @(tsee type)."
    :long
    (xdoc::topstring
     (xdoc::p
      "@('type-exp') has either 1 tree-list (for the non-paren
       alternatives @('atom-type-var')/@('array-type-var')/@('base-type')/
       @('bracket-type'), with the inner subtree giving the specific
       alternative) or 5 tree-lists (for the @('( ws type-exp-paren ws )')
       alternative)."))
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "type-exp")))
      (case (len treess)
        (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-exp"))
                ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
             (cond ((equal rulename? "atom-type-var")
                    (abs-atom-type-var inner))
                   ((equal rulename? "array-type-var")
                    (abs-array-type-var inner))
                   ((equal rulename? "base-type")
                    (b* (((okf bt) (abs-base-type inner)))
                      (make-type-base :type bt)))
                   ((equal rulename? "bracket-type")
                    (abs-bracket-type inner))
                   (t (reserrf (list :unexpected-type-exp-body
                                     (abnf::tree-info-for-error inner)))))))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
             (abs-type-exp-paren body-tree)))
        (otherwise
         (reserrf (list :type-exp-shape (len treess))))))
    :measure (abnf::tree-count tree))

  (define abs-type-exp-paren ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('type-exp-paren') to a @(tsee type)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-exp-paren"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "array-type") (abs-array-type inner))
            ((equal rulename? "arrow-type") (abs-arrow-type inner))
            ((equal rulename? "forall-type") (abs-forall-type inner))
            ((equal rulename? "pi-type") (abs-pi-type inner))
            ((equal rulename? "sigma-type") (abs-sigma-type inner))
            (t (reserrf (list :unexpected-type-exp-paren-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; bracket-type = "[" ws type-exp *( ws ispace ) ws "]"
  (define abs-bracket-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('bracket-type') to a @(tsee type) @(':bracket')."
    (b* (((okf (abnf::tree-list-tuple6 sub))
          (abnf::check-tree-nonleaf-6 tree "bracket-type"))
         ((okf te-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf elem) (abs-type-exp te-tree))
         ((okf ispaces) (abs-*-ws-ispace sub.4th))
         (shapes (ispaces-to-shapes ispaces)))
      (make-type-bracket :elem elem :shapes shapes))
    :measure (abnf::tree-count tree))

  ;; array-type = "A" ws type-exp ws shape
  (define abs-array-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract an @('array-type') to a @(tsee type) @(':array')."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "array-type"))
         ((okf te-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf shape-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf elem) (abs-type-exp te-tree))
         ((okf shape) (abs-shape shape-tree)))
      (make-type-array :elem elem :shape shape))
    :measure (abnf::tree-count tree))

  ;; arrow-type = ( "->" / %x2192 ) ws "(" *( ws type-exp ) ws ")" ws type-exp
  (define abs-arrow-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract an @('arrow-type') to a @(tsee type) @(':fun')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "arrow-type"))
         ((okf in) (abs-*-ws-type-exp sub.4th))
         ((okf out-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf out) (abs-type-exp out-tree)))
      (make-type-fun :in in :out out))
    :measure (abnf::tree-count tree))

  ;; forall-type = ( "Forall" / %x2200 ) ws "(" *( ws type-var ) ws ")"
  ;;               ws type-exp
  (define abs-forall-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('forall-type') to a @(tsee type) @(':forall')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "forall-type"))
         ((okf params) (abs-*-ws-type-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type-exp body-tree)))
      (make-type-forall :params params :body body))
    :measure (abnf::tree-count tree))

  ;; pi-type = ( "Pi" / %x03A0 ) ws "(" *( ws ispace-var ) ws ")"
  ;;           ws type-exp
  (define abs-pi-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('pi-type') to a @(tsee type) @(':pi')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "pi-type"))
         ((okf params) (abs-*-ws-ispace-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type-exp body-tree)))
      (make-type-pi :params params :body body))
    :measure (abnf::tree-count tree))

  ;; sigma-type = ( "Sigma" / %x03A3 ) ws "(" *( ws ispace-var ) ws ")"
  ;;              ws type-exp
  (define abs-sigma-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('sigma-type') to a @(tsee type) @(':sigma')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "sigma-type"))
         ((okf params) (abs-*-ws-ispace-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type-exp body-tree)))
      (make-type-sigma :params params :body body))
    :measure (abnf::tree-count tree))

  (define abs-ws-type-exp ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('( ws type-exp )') wrapper to a @(tsee type)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf te-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-type-exp te-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-type-exp ((trees abnf::tree-listp))
    :returns (tys type-list-resultp)
    :short "Abstract @('*( ws type-exp )') to a list of @(tsee type)s."
    (b* (((when (endp trees)) nil)
         ((okf ty) (abs-ws-type-exp (car trees)))
         ((okf rest) (abs-*-ws-type-exp (cdr trees))))
      (cons ty rest))
    :measure (abnf::tree-list-count trees))

  :ruler-extenders :all
  :verify-guards nil ; done below

  ///

  (verify-guards abs-type-exp)

  (fty::deffixequiv-mutual abs-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
