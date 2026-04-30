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
                    str::dec-digit-char-p
                    char-litp-when-result-not-error
                    char-lit-listp-when-result-not-error
                    simple-escapep-when-result-not-error
                    ascii-escapep-when-result-not-error
                    caret-escapep-when-result-not-error
                    num-escapep-when-result-not-error
                    escapep-when-result-not-error
                    oct-digit-char-listp-when-result-not-error
                    hex-digit-char-listp-when-result-not-error
                    str::oct-digit-char-p
                    str::hex-digit-char-p)))

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
;;
;; manual ``result'' predicates for fixtypes whose @(tsee fty::defresult)
;; disjointness proofs are awkward to set up
;;

(define expo-resultp (x)
  :returns (yes booleanp)
  :short "Recognizer for @(tsee expo) values or @(tsee reserrp) errors."
  (or (expop x) (reserrp x))
  ///
  (defrule expo-resultp-when-expop
    (implies (expop x) (expo-resultp x))
    :rule-classes (:rewrite :forward-chaining))
  (defrule expo-resultp-when-reserrp
    (implies (reserrp x) (expo-resultp x))
    :rule-classes (:rewrite :forward-chaining))
  (defrule expop-when-expo-resultp-not-error
    (implies (and (expo-resultp x) (not (reserrp x)))
             (expop x))
    :rule-classes (:rewrite :forward-chaining)))

(define expo-option-resultp (x)
  :returns (yes booleanp)
  :short "Recognizer for @(tsee expo-option) values or @(tsee reserrp) errors."
  (or (expo-optionp x) (reserrp x))
  ///
  (defrule expo-option-resultp-when-expo-optionp
    (implies (expo-optionp x) (expo-option-resultp x))
    :rule-classes (:rewrite :forward-chaining))
  (defrule expo-option-resultp-when-reserrp
    (implies (reserrp x) (expo-option-resultp x))
    :rule-classes (:rewrite :forward-chaining))
  (defrule expo-optionp-when-expo-option-resultp-not-error
    (implies (and (expo-option-resultp x) (not (reserrp x)))
             (expo-optionp x))
    :rule-classes (:rewrite :forward-chaining)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-num-val ((tree abnf::treep))
  :returns (val base-value-resultp)
  :short "Abstract a @('num-val') to a @(tsee base-value)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is
     @({
       num-val = [ \"+\" / \"-\" ] ( float-lit / decimal )
     })
     The CST has two tree-lists: an optional sign and a wrapper around
     either @('float-lit') or @('decimal').")
   (xdoc::p
    "We build either an @(tsee int-lit) (for @('decimal')) or a
     @(tsee float-lit) (for @('float-lit')) that preserves the
     source-level sign (absent vs.@ explicit @('+') vs.@ @('-'))
     and the decimal digits (including any leading zeros).  The
     numeric value is recovered later by the static/dynamic
     semantics."))
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
                ((unless (consp digits))
                 (reserrf :empty-decimal-digits-impossible)))
             (make-base-value-int :lit (make-int-lit :sign? sign?
                                                     :digits digits))))
          ((equal rulename? "float-lit")
           (abs-float-lit-as-base-value inner sign?))
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
       (abs-*-digit-tree-to-char trees)))

   (define abs-eE-group-to-upcase ((tree abnf::treep))
     :returns (upcase acl2::boolean-resultp)
     :parents nil
     :short "Abstract a @('( \"e\" / \"E\" )') group wrapper to a boolean
             (@('t') for upper, @('nil') for lower)."
     (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree nil))
          (lower-pass (abnf::check-tree-schars inner "e"))
          ((unless (reserrp lower-pass)) nil)
          (upper-pass (abnf::check-tree-schars inner "E"))
          ((unless (reserrp upper-pass)) t))
       (reserrf (list :unexpected-eE
                      (abnf::tree-info-for-error inner)))))

   ;; abs-expo and abs-expo-option use ``raw'' or-types in their :returns
   ;; clauses, since defresult of these defprods/options is awkward.
   ;; They are used only by abs-float-lit-as-base-value below.
   (define abs-expo ((tree abnf::treep))
     :returns (e expo-resultp)
     :parents nil
     :short "Abstract an @('exponent') CST to an @(tsee expo)."
     (b* (((okf (abnf::tree-list-tuple3 sub))
           (abnf::check-tree-nonleaf-3 tree "exponent"))
          ((okf eE-tree) (abnf::check-tree-list-1 sub.1st))
          ((okf upcase) (abs-eE-group-to-upcase eE-tree))
          ((okf opt-sign-tree) (abnf::check-tree-list-1 sub.2nd))
          ((okf sign?) (abs-optional-sign-to-option opt-sign-tree))
          ((okf digits) (abs-*-digit-tree-to-char sub.3rd))
          ((unless (consp digits))
           (reserrf :empty-exponent-digits-impossible)))
       (make-expo :upcase upcase :sign? sign? :digits digits)))

   (define abs-expo-option ((tree abnf::treep))
     :returns (e? expo-option-resultp)
     :parents nil
     :short "Abstract @('[ exponent ]') to an @(tsee expo-option)."
     (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
          ((when (endp treess)) (expo-option-none))
          ((okf trees) (abnf::check-tree-list-list-1 treess))
          ((okf inner) (abnf::check-tree-list-1 trees))
          ((okf e) (abs-expo inner)))
       (expo-option-some e)))

   ;; Build a base-value :float from a float-lit CST and the outer
   ;; num-val sign?.  Returning base-value-resultp avoids needing a
   ;; separate float-lit-result fixtype.
   ;;
   ;; float-lit = 1*DIGIT "." 1*DIGIT [ exponent ]   ; alt 1 (4 tree-lists)
   ;;           / 1*DIGIT exponent                   ; alt 2 (2 tree-lists)
   ;;
   ;; exponent = ( "e" / "E" ) [ "+" / "-" ] 1*DIGIT  ; 3 tree-lists
   (define abs-float-lit-as-base-value ((tree abnf::treep)
                                        (sign? sign-optionp))
     :returns (val base-value-resultp)
     :parents nil
     :short "Abstract a @('float-lit') CST to a @(tsee base-value) @(':float'),
             attaching the given outer @('sign?')."
     (b* (((okf treess) (abnf::check-tree-nonleaf tree "float-lit")))
       (case (len treess)
         (4
          ;; Alt 1: whole "." frac [exp]
          (b* (((okf (abnf::tree-list-tuple4 sub))
                (abnf::check-tree-list-list-4 treess))
               ((okf whole-digits) (abs-*-digit-tree-to-char sub.1st))
               ((unless (consp whole-digits))
                (reserrf :empty-whole-digits-impossible))
               ((okf frac-digits) (abs-*-digit-tree-to-char sub.3rd))
               ((unless (consp frac-digits))
                (reserrf :empty-frac-digits-impossible))
               ((okf opt-exp-tree) (abnf::check-tree-list-1 sub.4th))
               ((okf expo?)
                (abs-expo-option opt-exp-tree)))
            (make-base-value-float
             :lit (make-float-lit :sign? sign?
                                  :whole-digits whole-digits
                                  :frac-digits frac-digits
                                  :expo? expo?))))
         (2
          ;; Alt 2: whole exp
          (b* (((okf (abnf::tree-list-tuple2 sub))
                (abnf::check-tree-list-list-2 treess))
               ((okf whole-digits) (abs-*-digit-tree-to-char sub.1st))
               ((unless (consp whole-digits))
                (reserrf :empty-whole-digits-impossible))
               ((okf exp-tree) (abnf::check-tree-list-1 sub.2nd))
               ((okf expo) (abs-expo exp-tree)))
            (make-base-value-float
             :lit (make-float-lit :sign? sign?
                                  :whole-digits whole-digits
                                  :frac-digits nil
                                  :expo? (expo-option-some expo)))))
         (otherwise
          (reserrf (list :float-lit-shape (len treess)))))))))

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
;;
;; Escape sub-abstractors used by the escape branch of abs-char-lit.
;; (Defined before abs-char-lit because abs-char-lit calls
;; abs-escape-char.)
;;

(define abs-simple-escape ((tree abnf::treep))
  :returns (e simple-escape-resultp)
  :short "Abstract a @('char-escape') CST to a @(tsee simple-escape)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "char-escape"))
       ((okf leaf) (abnf::check-tree-leafterm inner))
       ((unless (and (consp leaf) (= (len leaf) 1)))
        (reserrf (list :char-escape-not-singleton leaf)))
       (nat (car leaf)))
    (cond ((eql nat #x61) (make-simple-escape-a))
          ((eql nat #x62) (make-simple-escape-b))
          ((eql nat #x66) (make-simple-escape-f))
          ((eql nat #x6E) (make-simple-escape-n))
          ((eql nat #x72) (make-simple-escape-r))
          ((eql nat #x74) (make-simple-escape-t))
          ((eql nat #x76) (make-simple-escape-v))
          ((eql nat #x5C) (make-simple-escape-bslash))
          ((eql nat #x22) (make-simple-escape-dquote))
          ((eql nat #x27) (make-simple-escape-squote))
          (t (reserrf (list :unexpected-char-escape nat))))))

(define nat-upcase ((n natp))
  :returns (m natp)
  :parents nil
  :short "Map ASCII lowercase to uppercase; pass others through."
  (if (and (<= #x61 (lnfix n)) (<= (lnfix n) #x7A))
      (- (lnfix n) #x20)
    (lnfix n)))

(define nats-upcase ((nats nat-listp))
  :returns (upcased nat-listp)
  :parents nil
  :short "Apply @(tsee nat-upcase) to each nat in a list."
  (cond ((endp nats) nil)
        (t (cons (nat-upcase (car nats))
                 (nats-upcase (cdr nats))))))

(define abs-ascii-escape ((tree abnf::treep))
  :returns (e ascii-escape-resultp)
  :short "Abstract an @('ascii-escape') CST to an @(tsee ascii-escape).
          Matching is case-insensitive (mirroring the parser)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "ascii-escape"))
       ((okf leaf) (abnf::check-tree-leafterm inner))
       (upper (nats-upcase leaf)))
    (cond ((equal upper '(78 85 76))
           (make-ascii-escape-nul-to-sp :code #x00))   ; NUL
          ((equal upper '(83 79 72))
           (make-ascii-escape-nul-to-sp :code #x01))   ; SOH
          ((equal upper '(83 84 88))
           (make-ascii-escape-nul-to-sp :code #x02))   ; STX
          ((equal upper '(69 84 88))
           (make-ascii-escape-nul-to-sp :code #x03))   ; ETX
          ((equal upper '(69 79 84))
           (make-ascii-escape-nul-to-sp :code #x04))   ; EOT
          ((equal upper '(69 78 81))
           (make-ascii-escape-nul-to-sp :code #x05))   ; ENQ
          ((equal upper '(65 67 75))
           (make-ascii-escape-nul-to-sp :code #x06))   ; ACK
          ((equal upper '(66 69 76))
           (make-ascii-escape-nul-to-sp :code #x07))   ; BEL
          ((equal upper '(66 83))
           (make-ascii-escape-nul-to-sp :code #x08))   ; BS
          ((equal upper '(72 84))
           (make-ascii-escape-nul-to-sp :code #x09))   ; HT
          ((equal upper '(76 70))
           (make-ascii-escape-nul-to-sp :code #x0A))   ; LF
          ((equal upper '(86 84))
           (make-ascii-escape-nul-to-sp :code #x0B))   ; VT
          ((equal upper '(70 70))
           (make-ascii-escape-nul-to-sp :code #x0C))   ; FF
          ((equal upper '(67 82))
           (make-ascii-escape-nul-to-sp :code #x0D))   ; CR
          ((equal upper '(83 79))
           (make-ascii-escape-nul-to-sp :code #x0E))   ; SO
          ((equal upper '(83 73))
           (make-ascii-escape-nul-to-sp :code #x0F))   ; SI
          ((equal upper '(68 76 69))
           (make-ascii-escape-nul-to-sp :code #x10))   ; DLE
          ((equal upper '(68 67 49))
           (make-ascii-escape-nul-to-sp :code #x11))   ; DC1
          ((equal upper '(68 67 50))
           (make-ascii-escape-nul-to-sp :code #x12))   ; DC2
          ((equal upper '(68 67 51))
           (make-ascii-escape-nul-to-sp :code #x13))   ; DC3
          ((equal upper '(68 67 52))
           (make-ascii-escape-nul-to-sp :code #x14))   ; DC4
          ((equal upper '(78 65 75))
           (make-ascii-escape-nul-to-sp :code #x15))   ; NAK
          ((equal upper '(83 89 78))
           (make-ascii-escape-nul-to-sp :code #x16))   ; SYN
          ((equal upper '(69 84 66))
           (make-ascii-escape-nul-to-sp :code #x17))   ; ETB
          ((equal upper '(67 65 78))
           (make-ascii-escape-nul-to-sp :code #x18))   ; CAN
          ((equal upper '(69 77))
           (make-ascii-escape-nul-to-sp :code #x19))   ; EM
          ((equal upper '(83 85 66))
           (make-ascii-escape-nul-to-sp :code #x1A))   ; SUB
          ((equal upper '(69 83 67))
           (make-ascii-escape-nul-to-sp :code #x1B))   ; ESC
          ((equal upper '(70 83))
           (make-ascii-escape-nul-to-sp :code #x1C))   ; FS
          ((equal upper '(71 83))
           (make-ascii-escape-nul-to-sp :code #x1D))   ; GS
          ((equal upper '(82 83))
           (make-ascii-escape-nul-to-sp :code #x1E))   ; RS
          ((equal upper '(85 83))
           (make-ascii-escape-nul-to-sp :code #x1F))   ; US
          ((equal upper '(83 80))
           (make-ascii-escape-nul-to-sp :code #x20))   ; SP
          ((equal upper '(68 69 76))
           (make-ascii-escape-del))                    ; DEL
          (t (reserrf (list :unknown-ascii-escape leaf))))))

(define abs-caret-escape ((tree abnf::treep))
  :returns (e caret-escape-resultp)
  :short "Abstract a @('caret-escape') CST to a @(tsee caret-escape).
          The control-character code is the input character minus
          @('#x40')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "caret-escape"))
       ((okf caret-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf ctrl-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf caret-leaf) (abnf::check-tree-leafterm caret-tree))
       ((unless (and (consp caret-leaf)
                     (= (len caret-leaf) 1)
                     (eql (car caret-leaf) #x5E)))
        (reserrf (list :unexpected-caret caret-leaf)))
       ((okf ctrl-leaf) (abnf::check-tree-leafterm ctrl-tree))
       ((unless (and (consp ctrl-leaf) (= (len ctrl-leaf) 1)))
        (reserrf (list :ctrl-not-singleton ctrl-leaf)))
       (ctrl-nat (car ctrl-leaf))
       ((unless (and (natp ctrl-nat)
                     (<= #x40 ctrl-nat)
                     (<= ctrl-nat #x5F)))
        (reserrf (list :ctrl-out-of-range ctrl-nat)))
       (code (- ctrl-nat #x40))
       ;; Redundant given the range check above, but makes the
       ;; caret-escape :require visible to the guard verifier.
       ((unless (and (natp code) (<= code #x1F)))
        (reserrf :caret-code-out-of-range-impossible)))
    (make-caret-escape :code code)))

(define abs-*-octal-leafterm-to-char ((trees abnf::tree-listp))
  :returns (chars oct-digit-char-list-resultp)
  :parents nil
  :short "Abstract a list of bare LEAFTERM trees (each a single octal
          digit nat in @('#x30..#x37')) to a list of
          @(tsee str::oct-digit-char)s."
  (b* (((when (endp trees)) nil)
       ((okf leaf) (abnf::check-tree-leafterm (car trees)))
       ((unless (and (consp leaf) (= (len leaf) 1)))
        (reserrf (list :octal-leaf-not-singleton leaf)))
       (nat (car leaf))
       ((unless (and (<= #x30 nat) (<= nat #x37)))
        (reserrf (list :octal-digit-out-of-range nat)))
       (c (code-char nat))
       ((okf rest) (abs-*-octal-leafterm-to-char (cdr trees))))
    (cons c rest)))

(define abs-*-hexdig-tree-to-char ((trees abnf::tree-listp))
  :returns (chars hex-digit-char-list-resultp)
  :parents nil
  :short "Abstract a list of @('hexdig') trees (each containing a single
          hex-digit nat) to a list of @(tsee str::hex-digit-char)s."
  (b* (((when (endp trees)) nil)
       ((okf inner) (abnf::check-tree-nonleaf-1-1 (car trees) "hexdig"))
       ((okf leaf) (abnf::check-tree-leafterm inner))
       ((unless (and (consp leaf) (= (len leaf) 1)))
        (reserrf (list :hexdig-leaf-not-singleton leaf)))
       (nat (car leaf))
       ((unless (or (and (<= #x30 nat) (<= nat #x39))
                    (and (<= #x41 nat) (<= nat #x46))
                    (and (<= #x61 nat) (<= nat #x66))))
        (reserrf (list :hex-digit-out-of-range nat)))
       (c (code-char nat))
       ((okf rest) (abs-*-hexdig-tree-to-char (cdr trees))))
    (cons c rest)))

(define abs-num-escape ((tree abnf::treep))
  :returns (e num-escape-resultp)
  :short "Abstract a @('num-escape') CST to a @(tsee num-escape)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "num-escape")))
    (case (len treess)
      (1
       ;; Decimal: 1*DIGIT, with sub.1st a list of `digit' trees.
       (b* (((okf digits-trees) (abnf::check-tree-list-list-1 treess))
            ((okf digits) (abs-*-digit-tree-to-char digits-trees))
            ((unless (consp digits))
             (reserrf :empty-num-escape-decimal-digits)))
         (make-num-escape-dec :digits digits)))
      (2
       ;; Octal `o' 1*octal-digit or hex `x' 1*HEXDIG.
       (b* (((okf (abnf::tree-list-tuple2 sub))
             (abnf::check-tree-list-list-2 treess))
            ((okf marker-tree) (abnf::check-tree-list-1 sub.1st))
            ((okf marker-leaf) (abnf::check-tree-leafterm marker-tree))
            ((unless (and (consp marker-leaf) (= (len marker-leaf) 1)))
             (reserrf (list :num-escape-marker-not-singleton marker-leaf)))
            (marker (car marker-leaf)))
         (cond ((or (eql marker #x6F) (eql marker #x4F))   ; 'o' / 'O'
                (b* (((okf digits) (abs-*-octal-leafterm-to-char sub.2nd))
                     ((unless (consp digits))
                      (reserrf :empty-num-escape-octal-digits)))
                  (make-num-escape-oct :digits digits)))
               ((or (eql marker #x78) (eql marker #x58))   ; 'x' / 'X'
                (b* (((okf digits) (abs-*-hexdig-tree-to-char sub.2nd))
                     ((unless (consp digits))
                      (reserrf :empty-num-escape-hex-digits)))
                  (make-num-escape-hex :digits digits)))
               (t (reserrf (list :unexpected-num-escape-marker marker))))))
      (otherwise
       (reserrf (list :num-escape-shape (len treess)))))))

(define abs-escape-char ((tree abnf::treep))
  :returns (e escape-resultp)
  :short "Abstract an @('escape-char') CST to an @(tsee escape)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "escape-char"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "char-escape")
           (b* (((okf s) (abs-simple-escape inner)))
             (make-escape-simple :escape s)))
          ((equal rulename? "ascii-escape")
           (b* (((okf a) (abs-ascii-escape inner)))
             (make-escape-ascii :escape a)))
          ((equal rulename? "caret-escape")
           (b* (((okf c) (abs-caret-escape inner)))
             (make-escape-caret :escape c)))
          ((equal rulename? "num-escape")
           (b* (((okf n) (abs-num-escape inner)))
             (make-escape-num :escape n)))
          (t (reserrf (list :unexpected-escape-char-body
                            (abnf::tree-info-for-error inner)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; char-lit and string-lit
;;

(define abs-char-lit ((tree abnf::treep))
  :returns (cl char-lit-resultp)
  :short "Abstract a @('char-lit') to a @(tsee char-lit)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar produces either 1 tree-list (non-escape: a single
     @(tsee abnf::tree-leafterm) with the character's code point) or
     2 tree-lists (escape: a leafterm for @('\\') and an
     @('escape-char') subtree)."))
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "char-lit")))
    (case (len treess)
      (1 (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
              ((okf inner) (abnf::check-tree-list-1 trees))
              ((okf leaf) (abnf::check-tree-leafterm inner))
              ((unless (consp leaf))
               (reserrf (list :empty-char-lit-leaf
                              (abnf::tree-info-for-error inner))))
              ((unless (= (len leaf) 1))
               (reserrf (list :char-lit-leaf-not-singleton leaf)))
              (code (car leaf))
              ((unless (and (natp code)
                            (or (and (<= 0 code) (<= code #x21))
                                (and (<= #x23 code) (<= code #x5B))
                                (and (<= #x5D code) (<= code #xD7FF))
                                (and (<= #xE000 code) (<= code #x10FFFF)))))
               (reserrf (list :char-lit-out-of-range code))))
           (make-char-lit-char :code code)))
      (2 (b* (((okf (abnf::tree-list-tuple2 sub))
              (abnf::check-tree-list-list-2 treess))
              ((okf bslash-tree) (abnf::check-tree-list-1 sub.1st))
              ((okf bslash-leaf) (abnf::check-tree-leafterm bslash-tree))
              ((unless (and (consp bslash-leaf)
                            (= (len bslash-leaf) 1)
                            (eql (car bslash-leaf) #x5C)))
               (reserrf (list :char-lit-escape-missing-backslash
                              bslash-leaf)))
              ((okf esc-tree) (abnf::check-tree-list-1 sub.2nd))
              ((okf e) (abs-escape-char esc-tree)))
           (make-char-lit-escape :escape e)))
      (otherwise
       (reserrf (list :char-lit-shape (len treess)))))))

(define abs-*-char-lit ((trees abnf::tree-listp))
  :returns (chars char-lit-list-resultp)
  :short "Abstract @('*char-lit') to a list of @(tsee char-lit)s."
  (b* (((when (endp trees)) nil)
       ((okf c) (abs-char-lit (car trees)))
       ((okf rest) (abs-*-char-lit (cdr trees))))
    (cons c rest)))

(define abs-string-lit ((tree abnf::treep))
  :returns (chars char-lit-list-resultp)
  :short "Abstract a @('string-lit') CST to a list of @(tsee char-lit)s
          (the chars between the surrounding @('DQUOTE')s)."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "string-lit")))
    (abs-*-char-lit sub.2nd)))

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
