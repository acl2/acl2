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

(include-book "kestrel/fty/dec-digit-char-list-result" :dir :system)
(include-book "kestrel/fty/hex-digit-char-list-result" :dir :system)
(include-book "kestrel/fty/nat-natlist-result" :dir :system)
(include-book "kestrel/fty/nat-list-result" :dir :system)
(include-book "kestrel/fty/oct-digit-char-list-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)
(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "projects/abnf/tree-operations/tree-utilities" :dir :system)
(include-book "unicode/utf8-encode" :dir :system)

(local
 (in-theory (enable abnf::treep-when-result-not-error
                    abnf::tree-listp-when-result-not-error
                    abnf::tree-list-listp-when-result-not-error
                    abnf::tree-list-tuple2p-when-result-not-error
                    abnf::tree-list-tuple3p-when-result-not-error
                    abnf::tree-list-tuple4p-when-result-not-error
                    abnf::tree-list-tuple5p-when-result-not-error
                    abnf::tree-list-tuple6p-when-result-not-error
                    abnf::tree-list-tuple7p-when-result-not-error
                    abnf::tree-list-tuple8p-when-result-not-error
                    abnf::tree-list-tuple9p-when-result-not-error
                    abnf::tree-list-tuple10p-when-result-not-error
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
                    base-litp-when-result-not-error
                    sign-optionp-when-result-not-error
                    str::dec-digit-char-listp-when-result-not-error
                    str::dec-digit-char-p
                    char-litp-when-result-not-error
                    char-lit-listp-when-result-not-error
                    char-escapep-when-result-not-error
                    ascii-escapep-when-result-not-error
                    caret-escapep-when-result-not-error
                    num-escapep-when-result-not-error
                    escapep-when-result-not-error
                    str::oct-digit-char-listp-when-result-not-error
                    str::hex-digit-char-listp-when-result-not-error
                    str::oct-digit-char-p
                    str::hex-digit-char-p
                    var+type?-p-when-result-not-error
                    var+type?-listp-when-result-not-error
                    type-optionp-when-result-not-error
                    type-list-optionp-when-result-not-error
                    ispace-list-optionp-when-result-not-error
                    type-var-list-optionp-when-result-not-error
                    ispace-var-list-optionp-when-result-not-error
                    exprp-when-result-not-error
                    expr-listp-when-result-not-error
                    atomp-when-result-not-error
                    atom-listp-when-result-not-error
                    bindp-when-result-not-error
                    bind-listp-when-result-not-error
                    importp-when-result-not-error
                    import-listp-when-result-not-error
                    declp-when-result-not-error
                    decl-listp-when-result-not-error
                    filep-when-result-not-error)))

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
    "."))
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
    (xdoc::seetopic "parser-interface" "@('decode-utf8-string')")
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
        (nats=>string (acl2::ustring=>utf8 nats))
      (reserrf (list :invalid-codepoints nats))))
  ///
  (defret stringp-of-abs-nats-to-string
    (implies (not (reserrp str))
             (stringp str))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-digit-to-nat ((tree abnf::treep))
  :returns (nat nat-resultp :hints (("Goal" :in-theory (enable natp))))
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
  :returns (nat nat-resultp)
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
  :returns (nat nat-resultp)
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
  :returns (n nat-resultp)
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
;; manual "result" predicates for fixtypes whose fty::defresult
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
  :returns (val base-lit-resultp)
  :short "Abstract a @('num-val') to a @(tsee base-lit)."
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
             (make-base-lit-int :lit (make-int-lit :sign? sign?
                                                   :digits digits))))
          ((equal rulename? "float-lit")
           (abs-float-lit-as-base-lit inner sign?))
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
   ;; They are used only by abs-float-lit-as-base-lit below.
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

   ;; Build a base-lit :float from a float-lit CST and the outer
   ;; num-val sign?.  Returning base-lit-resultp avoids needing a
   ;; separate float-lit-result fixtype.
   ;;
   ;; float-lit = 1*DIGIT "." 1*DIGIT [ exponent ]   ; alt 1 (4 tree-lists)
   ;;           / 1*DIGIT exponent                   ; alt 2 (2 tree-lists)
   ;;
   ;; exponent = ( "e" / "E" ) [ "+" / "-" ] 1*DIGIT  ; 3 tree-lists
   (define abs-float-lit-as-base-lit ((tree abnf::treep)
                                      (sign? sign-optionp))
     :returns (val base-lit-resultp)
     :parents nil
     :short "Abstract a @('float-lit') CST to a @(tsee base-lit) @(':float'),
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
            (make-base-lit-float
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
            (make-base-lit-float
             :lit (make-float-lit :sign? sign?
                                  :whole-digits whole-digits
                                  :frac-digits nil
                                  :expo? (expo-option-some expo)))))
         (otherwise
          (reserrf (list :float-lit-shape (len treess)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-base-val ((tree abnf::treep))
  :returns (val base-lit-resultp)
  :short "Abstract a @('base-val') to a @(tsee base-lit)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "base-val"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "bool-val")
           (b* (((okf b) (abs-bool-val inner)))
             (make-base-lit-bool :lit b)))
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

(define abs-char-escape ((tree abnf::treep))
  :returns (e char-escape-resultp)
  :short "Abstract a @('char-escape') CST to a @(tsee char-escape)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "char-escape"))
       ((okf leaf) (abnf::check-tree-leafterm inner))
       ((unless (and (consp leaf) (= (len leaf) 1)))
        (reserrf (list :char-escape-not-singleton leaf)))
       (nat (car leaf)))
    (cond ((eql nat #x61) (make-char-escape-a))
          ((eql nat #x62) (make-char-escape-b))
          ((eql nat #x66) (make-char-escape-f))
          ((eql nat #x6E) (make-char-escape-n))
          ((eql nat #x72) (make-char-escape-r))
          ((eql nat #x74) (make-char-escape-t))
          ((eql nat #x76) (make-char-escape-v))
          ((eql nat #x5C) (make-char-escape-bslash))
          ((eql nat #x22) (make-char-escape-dquote))
          ((eql nat #x27) (make-char-escape-squote))
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
           (b* (((okf s) (abs-char-escape inner)))
             (make-escape-char :escape s)))
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

;; ---- empty-escape and string-elem ----
;;
;; The grammar is
;;   empty-escape = "\&"
;;   string-elem  = char-lit / empty-escape
;; An empty-escape contributes no character to the surrounding string,
;; so abs-*-string-elem walks a tree-list and drops the empty-escape
;; trees, abstracting the char-lit ones to char-lit AST values.

(define abs-string-elem ((tree abnf::treep))
  :returns (chars char-lit-list-resultp)
  :short "Abstract a @('string-elem') CST to a list of @(tsee char-lit)s
          containing either zero (for an @('empty-escape')) or one
          (for a @('char-lit')) elements."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "string-elem"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "char-lit")
           (b* (((okf c) (abs-char-lit inner)))
             (list c)))
          ((equal rulename? "empty-escape")
           nil)
          (t (reserrf (list :unexpected-string-elem-body
                            (abnf::tree-info-for-error inner)))))))

(define abs-*-string-elem ((trees abnf::tree-listp))
  :returns (chars char-lit-list-resultp)
  :short "Abstract @('*string-elem') by flattening: an @('empty-escape')
          contributes 0 chars, a @('char-lit') contributes 1."
  (b* (((when (endp trees)) nil)
       ((okf elem) (abs-string-elem (car trees)))
       ((okf rest) (abs-*-string-elem (cdr trees))))
    (append elem rest)))

(define abs-string-lit ((tree abnf::treep))
  :returns (chars char-lit-list-resultp)
  :short "Abstract a @('string-lit') CST to a list of @(tsee char-lit)s
          (the chars between the surrounding @('DQUOTE')s, with
          @('\\&') empty escapes filtered out)."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "string-lit")))
    (abs-*-string-elem sub.2nd)))

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

(define abs-atom-type-var ((tree abnf::treep))
  :returns (ty type-var-resultp)
  :short "Abstract an @('atom-type-var') to a @(tsee type-var) @(':atom')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "atom-type-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "&"))
       ((when (reserrp sigil-pass))
        (reserrf (list :atom-type-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-type-var-atom :name name)))

(define abs-array-type-var ((tree abnf::treep))
  :returns (ty type-var-resultp)
  :short "Abstract an @('array-type-var') to a @(tsee type-var) @(':array')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "array-type-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "*"))
       ((when (reserrp sigil-pass))
        (reserrf (list :array-type-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-type-var-array :name name)))

(define abs-type-var ((tree abnf::treep))
  :returns (tv type-var-resultp)
  :short "Abstract a @('type-var') to a @(tsee type-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is @('type-var = atom-type-var / array-type-var')."))
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-var"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner))
       ((when (equal rulename? "atom-type-var")) (abs-atom-type-var inner))
       ((when (equal rulename? "array-type-var")) (abs-array-type-var inner)))
    (reserrf (list :unexpected-type-var-body
                   (abnf::tree-info-for-error inner)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-dim-ispace-var ((tree abnf::treep))
  :returns (ty ispace-var-resultp)
  :short "Abstract a @('dim-ispace-var') to an @(tsee ispace-var) @(':dim')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "dim-ispace-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "$"))
       ((when (reserrp sigil-pass))
        (reserrf (list :dim-ispace-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-ispace-var-dim :name name)))

(define abs-shape-ispace-var ((tree abnf::treep))
  :returns (ty ispace-var-resultp)
  :short "Abstract a @('shape-ispace-var') to a @(tsee ispace-var) @(':array')."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "shape-ispace-var"))
       ((okf sigil-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
       (sigil-pass (abnf::check-tree-ichars sigil-tree "@"))
       ((when (reserrp sigil-pass))
        (reserrf (list :shape-ispace-var-sigil
                       (abnf::tree-info-for-error sigil-tree))))
       ((okf name) (abs-identifier id-tree)))
    (make-ispace-var-shape :name name)))

(define abs-ispace-var ((tree abnf::treep))
  :returns (iv ispace-var-resultp)
  :short "Abstract an @('ispace-var') to an @(tsee ispace-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar is
     @('ispace-var = dim-ispace-var / shape-ispace-var.')"))
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "ispace-var"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner))
       ((when (equal rulename? "dim-ispace-var")) (abs-dim-ispace-var inner))
       ((when (equal rulename? "shape-ispace-var")) (abs-shape-ispace-var inner)))
    (reserrf (list :unexpected-ispace-var-body
                   (abnf::tree-info-for-error inner)))))

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
             (make-dim-const :val nat)))
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
  ;; *( ws dim ) repetition.  The operator is one of "+", "*", "-",
  ;; producing a dim-add, dim-mul, or dim-sub respectively.
  (define abs-dim-arith ((tree abnf::treep))
    :returns (d dim-resultp)
    :short "Abstract a @('dim-arith') to a @(tsee dim)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree "dim-arith"))
         ((okf op-tree) (abnf::check-tree-list-1 sub.1st))
         ((okf dims) (abs-*-ws-dim sub.2nd))
         (plus-pass (abnf::check-tree-ichars op-tree "+"))
         ((unless (reserrp plus-pass))
          (make-dim-add :dims dims))
         (mul-pass (abnf::check-tree-ichars op-tree "*"))
         ((unless (reserrp mul-pass))
          (make-dim-mul :dims dims))
         (sub-pass (abnf::check-tree-ichars op-tree "-"))
         ((unless (reserrp sub-pass))
          (make-dim-sub :dims dims)))
      (reserrf (list :dim-arith-op
                     (abnf::tree-info-for-error op-tree))))
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

  ;; shape has three alternatives, distinguished by the number of
  ;; tree-lists:
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
                ;; repetition list (a tree-listp).  The spliced elements
                ;; are kept as ispaces and a single dim stays an ispace :dim;
                ;; shape and ispace are mutually recursive.
                ((okf ispaces) (abs-*-ws-ispace sub.3rd)))
             (make-shape-splice :ispaces ispaces)))
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
;; types cluster
;;
;; Following the standard ABNF-parser convention used in PFCS, Aleo Leo,
;; etc., each named rule's CST has one tree-list per ABNF concatenation
;; element.  So arrow-type (8 elements) has 8 tree-lists, etc.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-types

  (define abs-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('type') to a @(tsee type)."
    :long
    (xdoc::topstring
     (xdoc::p
      "@('type') has either 1 tree-list (for the non-paren
       alternatives @('type-var')/@('base-type')/
       @('bracket-type'), with the inner subtree giving the specific
       alternative) or 5 tree-lists (for the @('( ws type-paren ws )')
       alternative)."))
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "type")))
      (case (len treess)
        (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type"))
                ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
             (cond ((equal rulename? "type-var")
                    (b* (((okf tv) (abs-type-var inner)))
                      (make-type-var :var tv)))
                   ((equal rulename? "base-type")
                    (b* (((okf bt) (abs-base-type inner)))
                      (make-type-base :type bt)))
                   ((equal rulename? "bracket-type")
                    (abs-bracket-type inner))
                   (t (reserrf (list :unexpected-type-body
                                     (abnf::tree-info-for-error inner)))))))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
             (abs-type-paren body-tree)))
        (otherwise
         (reserrf (list :type-shape (len treess))))))
    :measure (abnf::tree-count tree))

  (define abs-type-paren ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('type-paren') to a @(tsee type)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-paren"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "array-type") (abs-array-type inner))
            ((equal rulename? "arrow-type") (abs-arrow-type inner))
            ((equal rulename? "forall-type") (abs-forall-type inner))
            ((equal rulename? "pi-type") (abs-pi-type inner))
            ((equal rulename? "sigma-type") (abs-sigma-type inner))
            (t (reserrf (list :unexpected-type-paren-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; bracket-type = "[" ws type *( ws ispace ) ws "]"
  (define abs-bracket-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('bracket-type') to a @(tsee type) @(':bracket')."
    (b* (((okf (abnf::tree-list-tuple6 sub))
          (abnf::check-tree-nonleaf-6 tree "bracket-type"))
         ((okf te-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf elem) (abs-type te-tree))
         ((okf ispaces) (abs-*-ws-ispace sub.4th)))
      (make-type-bracket :elem elem :ispaces ispaces))
    :measure (abnf::tree-count tree))

  ;; array-type = "A" ws type ws ispace
  (define abs-array-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract an @('array-type') to a @(tsee type) @(':array')."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "array-type"))
         ((okf te-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf ispace-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf elem) (abs-type te-tree))
         ((okf ispace) (abs-ispace ispace-tree)))
      (make-type-array :elem elem :ispace ispace))
    :measure (abnf::tree-count tree))

  ;; arrow-type = ( "->" / %x2192 ) ws "(" *( ws type ) ws ")" ws type
  (define abs-arrow-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract an @('arrow-type') to a @(tsee type) @(':fun')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The grammar has two alternatives
       (see the parser's @('parse-arrow-type')):
       the parenthesized-list form produces 8 tree-lists,
       while the single-argument form produces 5;
       we dispatch on the count.
       The single-argument form abstracts to
       a @(':fun') with a singleton input list,
       so @('(-> T R)') and @('(-> (T) R)') have the same AST."))
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "arrow-type")))
      (case (len treess)
        (8 (b* (((okf (abnf::tree-list-tuple8 sub))
                 (abnf::check-tree-list-list-8 treess))
                ((okf in) (abs-*-ws-type sub.4th))
                ((okf out-tree) (abnf::check-tree-list-1 sub.8th))
                ((okf out) (abs-type out-tree)))
             (make-type-fun :in in :out out)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf in-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf in) (abs-type in-tree))
                ((okf out-tree) (abnf::check-tree-list-1 sub.5th))
                ((okf out) (abs-type out-tree)))
             (make-type-fun :in (list in) :out out)))
        (otherwise
         (reserrf (list :arrow-type-shape (len treess))))))
    :measure (abnf::tree-count tree))

  ;; forall-type = ( "Forall" / %x2200 ) ws "(" *( ws type-var ) ws ")"
  ;;               ws type
  (define abs-forall-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('forall-type') to
            a @(tsee type) @(':forall') or @(':foralln')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A universal type with one variable becomes
       a unary universal type @(':forall');
       one with two or more variables becomes
       an n-ary universal type @(':foralln')
       (see @(tsee type))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "forall-type"))
         ((okf params) (abs-*-ws-type-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-type-forall :param (car params) :body body)
        (make-type-foralln :params params :body body)))
    :measure (abnf::tree-count tree))

  ;; pi-type = ( "Pi" / %x03A0 ) ws "(" *( ws ispace-var ) ws ")"
  ;;           ws type
  (define abs-pi-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('pi-type') to a @(tsee type) @(':pi') or @(':pin')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A product type with one variable becomes
       a unary product type @(':pi');
       one with two or more variables becomes
       an n-ary product type @(':pin')
       (see @(tsee type))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "pi-type"))
         ((okf params) (abs-*-ws-ispace-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-type-pi :param (car params) :body body)
        (make-type-pin :params params :body body)))
    :measure (abnf::tree-count tree))

  ;; sigma-type = ( "Sigma" / %x03A3 ) ws "(" *( ws ispace-var ) ws ")"
  ;;              ws type
  (define abs-sigma-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('sigma-type') to
            a @(tsee type) @(':sigma') or @(':sigman')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A sum type with one variable becomes
       a unary sum type @(':sigma');
       one with two or more variables becomes
       an n-ary sum type @(':sigman')
       (see @(tsee type))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "sigma-type"))
         ((okf params) (abs-*-ws-ispace-var sub.4th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf body) (abs-type body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-type-sigma :param (car params) :body body)
        (make-type-sigman :params params :body body)))
    :measure (abnf::tree-count tree))

  (define abs-ws-type ((tree abnf::treep))
    :returns (ty type-resultp)
    :short "Abstract a @('( ws type )') wrapper to a @(tsee type)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf te-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-type te-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-type ((trees abnf::tree-listp))
    :returns (tys type-list-resultp)
    :short "Abstract @('*( ws type )') to a list of @(tsee type)s."
    (b* (((when (endp trees)) nil)
         ((okf ty) (abs-ws-type (car trees)))
         ((okf rest) (abs-*-ws-type (cdr trees))))
      (cons ty rest))
    :measure (abnf::tree-list-count trees))

  :ruler-extenders :all
  :verify-guards nil ; done below

  ///

  (verify-guards abs-type)

  (fty::deffixequiv-mutual abs-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; pat / pattern repetitions
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; pat = "(" ws identifier ws type ws ")"
(define abs-pat ((tree abnf::treep))
  :returns (vt var+type?-resultp)
  :short "Abstract a @('pat') to a @(tsee var+type?)."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "pat"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf te-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf name) (abs-identifier id-tree))
       ((okf ty) (abs-type te-tree)))
    (make-var+type? :var name :type? ty)))

(define abs-ws-pat ((tree abnf::treep))
  :returns (vt var+type?-resultp)
  :short "Abstract a @('( ws pat )') wrapper to a @(tsee var+type?)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf pat-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-pat pat-tree)))

(define abs-*-ws-pat ((trees abnf::tree-listp))
  :returns (vts var+type?-list-resultp)
  :short "Abstract @('*( ws pat )') to a @(tsee var+type?-list)."
  (b* (((when (endp trees)) nil)
       ((okf vt) (abs-ws-pat (car trees)))
       ((okf rest) (abs-*-ws-pat (cdr trees))))
    (cons vt rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; type-args / ispace-args / type-vars / ispace-vars
;;
;; All four rules share the same shape: either "(" *( ws X ) ws ")" (4 tree-
;; lists) for the explicit-list form, or just the leafterm "_" (1 tree-list
;; with a single leafterm) for the absent form.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-type-args ((tree abnf::treep))
  :returns (tlo type-list-option-resultp)
  :short "Abstract a @('type-args') to a @(tsee type-list-option)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "type-args")))
    (case (len treess)
      (4 (b* (((okf (abnf::tree-list-tuple4 sub))
               (abnf::check-tree-list-list-4 treess))
              ((okf tys) (abs-*-ws-type sub.2nd)))
           (make-type-list-option-some :val tys)))
      (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-args"))
              (us-pass (abnf::check-tree-ichars inner "_"))
              ((when (reserrp us-pass))
               (reserrf (list :type-args-not-underscore
                              (abnf::tree-info-for-error inner)))))
           (make-type-list-option-none)))
      (otherwise
       (reserrf (list :type-args-shape (len treess)))))))

(define abs-ispace-args ((tree abnf::treep))
  :returns (ilo ispace-list-option-resultp)
  :short "Abstract an @('ispace-args') to an @(tsee ispace-list-option)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "ispace-args")))
    (case (len treess)
      (4 (b* (((okf (abnf::tree-list-tuple4 sub))
               (abnf::check-tree-list-list-4 treess))
              ((okf is) (abs-*-ws-ispace sub.2nd)))
           (make-ispace-list-option-some :val is)))
      (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "ispace-args"))
              (us-pass (abnf::check-tree-ichars inner "_"))
              ((when (reserrp us-pass))
               (reserrf (list :ispace-args-not-underscore
                              (abnf::tree-info-for-error inner)))))
           (make-ispace-list-option-none)))
      (otherwise
       (reserrf (list :ispace-args-shape (len treess)))))))

(define abs-type-vars ((tree abnf::treep))
  :returns (tvlo type-var-list-option-resultp)
  :short "Abstract a @('type-vars') to a @(tsee type-var-list-option)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "type-vars")))
    (case (len treess)
      (4 (b* (((okf (abnf::tree-list-tuple4 sub))
               (abnf::check-tree-list-list-4 treess))
              ((okf tvs) (abs-*-ws-type-var sub.2nd)))
           (make-type-var-list-option-some :val tvs)))
      (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "type-vars"))
              (us-pass (abnf::check-tree-ichars inner "_"))
              ((when (reserrp us-pass))
               (reserrf (list :type-vars-not-underscore
                              (abnf::tree-info-for-error inner)))))
           (make-type-var-list-option-none)))
      (otherwise
       (reserrf (list :type-vars-shape (len treess)))))))

(define abs-ispace-vars ((tree abnf::treep))
  :returns (ivlo ispace-var-list-option-resultp)
  :short "Abstract an @('ispace-vars') to an @(tsee ispace-var-list-option)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree "ispace-vars")))
    (case (len treess)
      (4 (b* (((okf (abnf::tree-list-tuple4 sub))
               (abnf::check-tree-list-list-4 treess))
              ((okf ivs) (abs-*-ws-ispace-var sub.2nd)))
           (make-ispace-var-list-option-some :val ivs)))
      (1 (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "ispace-vars"))
              (us-pass (abnf::check-tree-ichars inner "_"))
              ((when (reserrp us-pass))
               (reserrf (list :ispace-vars-not-underscore
                              (abnf::tree-info-for-error inner)))))
           (make-ispace-var-list-option-none)))
      (otherwise
       (reserrf (list :ispace-vars-shape (len treess)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; colon-type and the optional-type-annotation inline option
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; colon-type = ":" ws type
(define abs-colon-type ((tree abnf::treep))
  :returns (ty type-resultp)
  :short "Abstract a @('colon-type') to a @(tsee type)."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "colon-type"))
       ((okf te-tree) (abnf::check-tree-list-1 sub.3rd)))
    (abs-type te-tree)))

;; The inline option [ ws colon-type ] used in fun-sig/tfun-sig/ifun-sig.
;; The CST is an anonymous nonleaf whose branches are either
;; - empty (absent annotation), or
;; - two tree-lists (ws-tree)(colon-type-tree) (present annotation).
(define abs-optional-type-annotation ((tree abnf::treep))
  :returns (ty? type-option-resultp)
  :short "Abstract a @('[ ws colon-type ]') to a @(tsee type-option)."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
       ((when (endp treess)) (type-option-none))
       ((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-list-list-2 treess))
       ((okf ct-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf ty) (abs-colon-type ct-tree)))
    (type-option-some ty)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; ispace-var-ws and its repetition (used by unbox-spec)
;;
;; This wrapper has the elements in reverse order from the usual
;; *( ws X ) wrappers: ispace-var first, ws second.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-ispace-var-ws ((tree abnf::treep))
  :returns (iv ispace-var-resultp)
  :short "Abstract a @('( ispace-var ws )') wrapper to an @(tsee ispace-var)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf iv-tree) (abnf::check-tree-list-1 sub.1st)))
    (abs-ispace-var iv-tree)))

(define abs-*-ispace-var-ws ((trees abnf::tree-listp))
  :returns (ivs ispace-var-list-resultp)
  :short "Abstract @('*( ispace-var ws )') to an @(tsee ispace-var-list)."
  (b* (((when (endp trees)) nil)
       ((okf iv) (abs-ispace-var-ws (car trees)))
       ((okf rest) (abs-*-ispace-var-ws (cdr trees))))
    (cons iv rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Abstractor-internal defprods for the *-sig CSTs.
;;
;; Each *-fun-bind / val-bind alt 2 is factored at the grammar level into
;; an outer shell plus an inner -sig sub-rule.  The corresponding inner
;; abstractor returns a small defprod that captures the components of the
;; sub-rule; the outer abstractor consumes that defprod to construct the
;; corresponding bind AST node.  These defprods do not appear in any
;; AST output; they are purely abstractor-internal.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-sig-info
  :short "Abstractor-internal record holding the components of a @('fun-sig')
          CST: function name, value parameters, and optional return type."
  ((name string)
   (params var+type?-list)
   (ret-type type-option))
  :pred fun-sig-info-p)

(fty::defresult fun-sig-info-result
  :short "Fixtype of @(tsee fun-sig-info) and errors."
  :ok fun-sig-info
  :pred fun-sig-info-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tfun-sig-info
  :short "Abstractor-internal record holding the components of a @('tfun-sig')
          CST: function name, type parameters, and optional return type."
  ((name string)
   (params type-var-list)
   (ret-type type-option))
  :pred tfun-sig-info-p)

(fty::defresult tfun-sig-info-result
  :short "Fixtype of @(tsee tfun-sig-info) and errors."
  :ok tfun-sig-info
  :pred tfun-sig-info-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ifun-sig-info
  :short "Abstractor-internal record holding the components of an
          @('ifun-sig') CST: function name, ispace parameters, and optional
          return type."
  ((name string)
   (params ispace-var-list)
   (ret-type type-option))
  :pred ifun-sig-info-p)

(fty::defresult ifun-sig-info-result
  :short "Fixtype of @(tsee ifun-sig-info) and errors."
  :ok ifun-sig-info
  :pred ifun-sig-info-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod at-fun-sig-info
  :short "Abstractor-internal record holding the components of an
          @('at-fun-sig') CST: function name, optional type/ispace parameter
          lists, value parameters, and (mandatory) return type."
  ((name string)
   (tparams type-var-list-option)
   (iparams ispace-var-list-option)
   (params var+type?-list)
   (ret-type type))
  :pred at-fun-sig-info-p)

(fty::defresult at-fun-sig-info-result
  :short "Fixtype of @(tsee at-fun-sig-info) and errors."
  :ok at-fun-sig-info
  :pred at-fun-sig-info-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; *-sig abstractors
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable fun-sig-info-p-when-result-not-error
                    tfun-sig-info-p-when-result-not-error
                    ifun-sig-info-p-when-result-not-error
                    at-fun-sig-info-p-when-result-not-error)))

;; val-typed-sig = identifier ws colon-type
(define abs-val-typed-sig ((tree abnf::treep))
  :returns (vt var+type?-resultp)
  :short "Abstract a @('val-typed-sig') to a @(tsee var+type?)."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "val-typed-sig"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf ct-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf name) (abs-identifier id-tree))
       ((okf ty) (abs-colon-type ct-tree)))
    (make-var+type? :var name :type? ty)))

;; fun-sig = identifier *( ws pat ) [ ws colon-type ]
(define abs-fun-sig ((tree abnf::treep))
  :returns (info fun-sig-info-resultp)
  :short "Abstract a @('fun-sig') to a @(tsee fun-sig-info)."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "fun-sig"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf opt-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf name) (abs-identifier id-tree))
       ((okf params) (abs-*-ws-pat sub.2nd))
       ((okf ret-type) (abs-optional-type-annotation opt-tree)))
    (make-fun-sig-info :name name :params params :ret-type ret-type)))

;; tfun-sig = identifier ws "(" *( ws type-var ) ws ")" [ ws colon-type ]
(define abs-tfun-sig ((tree abnf::treep))
  :returns (info tfun-sig-info-resultp)
  :short "Abstract a @('tfun-sig') to a @(tsee tfun-sig-info)."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "tfun-sig"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf opt-tree) (abnf::check-tree-list-1 sub.7th))
       ((okf name) (abs-identifier id-tree))
       ((okf params) (abs-*-ws-type-var sub.4th))
       ((okf ret-type) (abs-optional-type-annotation opt-tree)))
    (make-tfun-sig-info :name name :params params :ret-type ret-type)))

;; ifun-sig = identifier ws "(" *( ws ispace-var ) ws ")" [ ws colon-type ]
(define abs-ifun-sig ((tree abnf::treep))
  :returns (info ifun-sig-info-resultp)
  :short "Abstract an @('ifun-sig') to an @(tsee ifun-sig-info)."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "ifun-sig"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf opt-tree) (abnf::check-tree-list-1 sub.7th))
       ((okf name) (abs-identifier id-tree))
       ((okf params) (abs-*-ws-ispace-var sub.4th))
       ((okf ret-type) (abs-optional-type-annotation opt-tree)))
    (make-ifun-sig-info :name name :params params :ret-type ret-type)))

;; at-fun-sig = "@" ws identifier ws type-vars ws ispace-vars
;;              *( ws pat ) ws colon-type
(define abs-at-fun-sig ((tree abnf::treep))
  :returns (info at-fun-sig-info-resultp)
  :short "Abstract an @('at-fun-sig') to an @(tsee at-fun-sig-info)."
  (b* (((okf (abnf::tree-list-tuple10 sub))
        (abnf::check-tree-nonleaf-10 tree "at-fun-sig"))
       ((okf id-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf tvs-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf ivs-tree) (abnf::check-tree-list-1 sub.7th))
       ((okf ct-tree) (abnf::check-tree-list-1 sub.10th))
       ((okf name) (abs-identifier id-tree))
       ((okf tparams) (abs-type-vars tvs-tree))
       ((okf iparams) (abs-ispace-vars ivs-tree))
       ((okf params) (abs-*-ws-pat sub.8th))
       ((okf ret-type) (abs-colon-type ct-tree)))
    (make-at-fun-sig-info :name name
                          :tparams tparams
                          :iparams iparams
                          :params params
                          :ret-type ret-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; type-bind and ispace-bind: pre-cluster (don't recurse into exp/atom/bind).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; type-bind = "type" ws type-var ws type
(define abs-type-bind ((tree abnf::treep))
  :returns (b bind-resultp)
  :short "Abstract a @('type-bind') to a @(tsee bind) @(':type')."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "type-bind"))
       ((okf tv-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf te-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf tv) (abs-type-var tv-tree))
       ((okf ty) (abs-type te-tree)))
    (make-bind-type :var tv :type ty)))

;; ispace-bind = "ispace" ws ispace-var ws ispace
(define abs-ispace-bind ((tree abnf::treep))
  :returns (b bind-resultp)
  :short "Abstract an @('ispace-bind') to a @(tsee bind) @(':ispace')."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "ispace-bind"))
       ((okf iv-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf is-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf iv) (abs-ispace-var iv-tree))
       ((okf is) (abs-ispace is-tree)))
    (make-bind-ispace :var iv :ispace is)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; unbox-spec-info: like the *-sig-info defprods, but holding the
;; components of an unbox-spec CST.  Has an expr field, so it must come
;; after the AST's exprs/atoms/binds deftypes (which is in
;; abstract-syntax-trees.lisp, already included).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod unbox-spec-info
  :short "Abstractor-internal record holding the components of an
          @('unbox-spec') CST: ispace-var binders, value-var binder, and
          target expression yielding the box being unboxed."
  ((ispaces ispace-var-list)
   (var string)
   (target expr))
  :pred unbox-spec-info-p)

(fty::defresult unbox-spec-info-result
  :short "Fixtype of @(tsee unbox-spec-info) and errors."
  :ok unbox-spec-info
  :pred unbox-spec-info-resultp)

(local (in-theory (enable unbox-spec-info-p-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Expressions, atoms, and bindings cluster
;;
;; Mutually recursive because:
;;   exp -> atom -> lambda -> exp
;;   exp -> let-exp -> bind -> val-bind -> exp
;;   exp -> unbox-exp -> unbox-spec -> exp
;;   etc.
;;
;; Pre-cluster helpers (abs-pat, abs-fun-sig, abs-tfun-sig, abs-ifun-sig,
;; abs-at-fun-sig, abs-val-typed-sig, abs-type-args, abs-ispace-args,
;; abs-type-vars, abs-ispace-vars, abs-optional-type-annotation,
;; abs-colon-type, abs-*-ws-pat, abs-*-ispace-var-ws) handle the parts that
;; do not transitively reach back into exp/atom/bind.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-exprs/atoms/binds

  ;; ------------------------------------------------------------------
  ;; Expressions
  ;; ------------------------------------------------------------------

  (define abs-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('exp') to an @(tsee expr)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "exp"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "atom")
             (b* (((okf a) (abs-atom inner)))
               ;; A bare atom is abstracted to an atom expression, preserving
               ;; the information that it was written as an atom; desugaring
               ;; later turns it into a rank-0 array (array [] a).
               (make-expr-atom :atom a)))
            ((equal rulename? "bracket-frame")
             (abs-bracket-frame inner))
            ((equal rulename? "identifier")
             (b* (((okf name) (abs-identifier inner)))
               (make-expr-var :name name)))
            ((equal rulename? "string-lit")
             (b* (((okf chars) (abs-string-lit inner)))
               (make-expr-string :chars chars)))
            ((equal rulename? "paren-exp")
             (abs-paren-exp inner))
            (t (reserrf (list :unexpected-exp-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; bracket-frame = "[" ws exp *( ws exp ) ws "]"
  (define abs-bracket-frame ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('bracket-frame') to an @(tsee expr) @(':bracket')."
    (b* (((okf (abnf::tree-list-tuple6 sub))
          (abnf::check-tree-nonleaf-6 tree "bracket-frame"))
         ((okf e1-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf e1) (abs-exp e1-tree))
         ((okf rest) (abs-*-ws-exp sub.4th)))
      (make-expr-bracket :exprs (cons e1 rest)))
    :measure (abnf::tree-count tree))

  ;; paren-exp = "(" ws paren-exp-body ws ")"
  (define abs-paren-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('paren-exp') to an @(tsee expr)."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "paren-exp"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
      (abs-paren-exp-body body-tree))
    :measure (abnf::tree-count tree))

  (define abs-paren-exp-body ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('paren-exp-body') to an @(tsee expr)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "paren-exp-body"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "array-exp") (abs-array-exp inner))
            ((equal rulename? "frame-exp") (abs-frame-exp inner))
            ((equal rulename? "tapp-exp") (abs-tapp-exp inner))
            ((equal rulename? "iapp-exp") (abs-iapp-exp inner))
            ((equal rulename? "unbox-exp") (abs-unbox-exp inner))
            ((equal rulename? "let-exp") (abs-let-exp inner))
            ((equal rulename? "at-app-exp") (abs-at-app-exp inner))
            ((equal rulename? "app-exp") (abs-app-exp inner))
            (t (reserrf (list :unexpected-paren-exp-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; app-exp = exp *( ws exp )
  (define abs-app-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('app-exp') to
            an @(tsee expr) @(':app') or @(':appn')."
    :long
    (xdoc::topstring
     (xdoc::p
      "An application to one argument becomes
       a unary term application @(':app');
       an application to two or more arguments becomes
       an n-ary term application @(':appn')
       (see @(tsee expr))."))
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree "app-exp"))
         ((okf fun-tree) (abnf::check-tree-list-1 sub.1st))
         ((okf fun) (abs-exp fun-tree))
         ((okf args) (abs-*-ws-exp sub.2nd)))
      (if (and (consp args)
               (endp (cdr args)))
          (make-expr-app :fun fun :arg (car args))
        (make-expr-appn :fun fun :args args)))
    :measure (abnf::tree-count tree))

  ;; array-exp = "array" ws shape-lit *( ws atom )
  ;;           / "array" ws shape-lit ws type
  (define abs-array-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('array-exp') to an @(tsee expr)
            @(':array') or @(':array-empty')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The non-empty alternative has 4 branches
       (@('array'), @('ws'), @('shape-lit'), @('*( ws atom )')) and
       abstracts to @(':array').
       The empty alternative has 5 branches
       (@('array'), @('ws'), @('shape-lit'), @('ws'), @('type')) and
       abstracts to @(':array-empty'), with the element type taken from the
       @('type')."))
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "array-exp")))
      (case (len treess)
        (4 (b* (((okf (abnf::tree-list-tuple4 sub))
                 (abnf::check-tree-nonleaf-4 tree "array-exp"))
                ((okf sl-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf dims) (abs-shape-lit sl-tree))
                ((okf atoms) (abs-*-ws-atom sub.4th)))
             (make-expr-array :dims dims :atoms atoms)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-nonleaf-5 tree "array-exp"))
                ((okf sl-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf dims) (abs-shape-lit sl-tree))
                ((okf te-tree) (abnf::check-tree-list-1 sub.5th))
                ((okf type) (abs-type te-tree)))
             (make-expr-array-empty :dims dims :type type)))
        (otherwise
         (reserrf (list :array-exp-shape (len treess))))))
    :measure (abnf::tree-count tree))

  ;; frame-exp = "frame" ws shape-lit *( ws exp )
  ;;           / "frame" ws shape-lit ws type
  (define abs-frame-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('frame-exp') to an @(tsee expr)
            @(':frame') or @(':frame-empty')."
    :long
    (xdoc::topstring
     (xdoc::p
      "The non-empty alternative has 4 branches and abstracts to
       @(':frame'); the empty alternative has 5 branches and abstracts to
       @(':frame-empty'), with the element type taken from the
       @('type').  See @(tsee abs-array-exp)."))
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "frame-exp")))
      (case (len treess)
        (4 (b* (((okf (abnf::tree-list-tuple4 sub))
                 (abnf::check-tree-nonleaf-4 tree "frame-exp"))
                ((okf sl-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf dims) (abs-shape-lit sl-tree))
                ((okf exprs) (abs-*-ws-exp sub.4th)))
             (make-expr-frame :dims dims :exprs exprs)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-nonleaf-5 tree "frame-exp"))
                ((okf sl-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf dims) (abs-shape-lit sl-tree))
                ((okf te-tree) (abnf::check-tree-list-1 sub.5th))
                ((okf type) (abs-type te-tree)))
             (make-expr-frame-empty :dims dims :type type)))
        (otherwise
         (reserrf (list :frame-exp-shape (len treess))))))
    :measure (abnf::tree-count tree))

  ;; tapp-exp = "t-app" ws exp *( ws type )
  (define abs-tapp-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('tapp-exp') to
            an @(tsee expr) @(':tapp') or @(':tappn')."
    :long
    (xdoc::topstring
     (xdoc::p
      "An application to one type argument becomes
       a unary type application @(':tapp');
       an application to two or more type arguments becomes
       an n-ary type application @(':tappn')
       (see @(tsee expr))."))
    (b* (((okf (abnf::tree-list-tuple4 sub))
          (abnf::check-tree-nonleaf-4 tree "tapp-exp"))
         ((okf fun-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf fun) (abs-exp fun-tree))
         ((okf args) (abs-*-ws-type sub.4th)))
      (if (and (consp args)
               (endp (cdr args)))
          (make-expr-tapp :fun fun :arg (car args))
        (make-expr-tappn :fun fun :args args)))
    :measure (abnf::tree-count tree))

  ;; iapp-exp = "i-app" ws exp *( ws ispace )
  (define abs-iapp-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('iapp-exp') to
            an @(tsee expr) @(':iapp') or @(':iappn')."
    :long
    (xdoc::topstring
     (xdoc::p
      "An application to one ispace argument becomes
       a unary ispace application @(':iapp');
       an application to two or more ispace arguments becomes
       an n-ary ispace application @(':iappn')
       (see @(tsee expr))."))
    (b* (((okf (abnf::tree-list-tuple4 sub))
          (abnf::check-tree-nonleaf-4 tree "iapp-exp"))
         ((okf fun-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf fun) (abs-exp fun-tree))
         ((okf args) (abs-*-ws-ispace sub.4th)))
      (if (and (consp args)
               (endp (cdr args)))
          (make-expr-iapp :fun fun :arg (car args))
        (make-expr-iappn :fun fun :args args)))
    :measure (abnf::tree-count tree))

  ;; unbox-exp = "unbox" ws "(" ws unbox-spec ws ")" ws exp
  (define abs-unbox-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('unbox-exp') to
            an @(tsee expr) @(':unbox') or @(':unboxn')."
    :long
    (xdoc::topstring
     (xdoc::p
      "An unboxing with one ispace variable becomes
       a unary unboxing @(':unbox');
       one with two or more ispace variables becomes
       an n-ary unboxing @(':unboxn')
       (see @(tsee expr))."))
    (b* (((okf (abnf::tree-list-tuple9 sub))
          (abnf::check-tree-nonleaf-9 tree "unbox-exp"))
         ((okf spec-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf body-tree) (abnf::check-tree-list-1 sub.9th))
         ((okf info) (abs-unbox-spec spec-tree))
         ((okf body) (abs-exp body-tree))
         (ispaces (unbox-spec-info->ispaces info))
         (var (unbox-spec-info->var info))
         (target (unbox-spec-info->target info)))
      (if (and (consp ispaces)
               (endp (cdr ispaces)))
          (make-expr-unbox :ispace (car ispaces)
                           :var var
                           :target target
                           :body body
                           :type? nil)
        (make-expr-unboxn :ispaces ispaces
                          :var var
                          :target target
                          :body body
                          :type? nil)))
    :measure (abnf::tree-count tree))

  ;; unbox-spec = *( ispace-var ws ) identifier ws exp
  (define abs-unbox-spec ((tree abnf::treep))
    :returns (info unbox-spec-info-resultp)
    :short "Abstract an @('unbox-spec') to an @(tsee unbox-spec-info)."
    (b* (((okf (abnf::tree-list-tuple4 sub))
          (abnf::check-tree-nonleaf-4 tree "unbox-spec"))
         ((okf id-tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf e-tree) (abnf::check-tree-list-1 sub.4th))
         ((okf ispaces) (abs-*-ispace-var-ws sub.1st))
         ((okf name) (abs-identifier id-tree))
         ((okf target) (abs-exp e-tree)))
      (make-unbox-spec-info :ispaces ispaces :var name :target target))
    :measure (abnf::tree-count tree))

  ;; let-exp = "let" ws "(" *( ws bind ) ws ")" ws exp
  (define abs-let-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('let-exp') to an @(tsee expr) @(':let')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "let-exp"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf binds) (abs-*-ws-bind sub.4th))
         ((okf body) (abs-exp body-tree)))
      (make-expr-let :binds binds :body body))
    :measure (abnf::tree-count tree))

  ;; at-app-exp = "@" ws exp ws type-args ws ispace-args *( ws exp )
  (define abs-at-app-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract an @('at-app-exp') to an @(tsee expr) @(':capp')."
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "at-app-exp"))
         ((okf fun-tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf ta-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf ia-tree) (abnf::check-tree-list-1 sub.7th))
         ((okf fun) (abs-exp fun-tree))
         ((okf targs) (abs-type-args ta-tree))
         ((okf iargs) (abs-ispace-args ia-tree))
         ((okf args) (abs-*-ws-exp sub.8th)))
      (make-expr-capp :fun fun :targs targs :iargs iargs :args args))
    :measure (abnf::tree-count tree))

  ;; ------------------------------------------------------------------
  ;; Atoms
  ;; ------------------------------------------------------------------

  ;; atom = base-val / "(" ws atom-body ws ")"
  (define abs-atom ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract an @('atom') to an @(tsee atom)."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "atom")))
      (case (len treess)
        (1 (b* (((okf inner)
                 (abnf::check-tree-nonleaf-1-1 tree "atom"))
                ((okf rulename?) (abnf::check-tree-nonleaf? inner))
                ((unless (equal rulename? "base-val"))
                 (reserrf (list :unexpected-atom-body
                                (abnf::tree-info-for-error inner))))
                ((okf bv) (abs-base-val inner)))
             (make-atom-base :lit bv)))
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
             (abs-atom-body body-tree)))
        (otherwise
         (reserrf (list :atom-shape (len treess))))))
    :measure (abnf::tree-count tree))

  (define abs-atom-body ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract an @('atom-body') to an @(tsee atom)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "atom-body"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "lambda") (abs-lambda inner))
            ((equal rulename? "type-lambda") (abs-type-lambda inner))
            ((equal rulename? "ispace-lambda") (abs-ispace-lambda inner))
            ((equal rulename? "box-expr") (abs-box-expr inner))
            (t (reserrf (list :unexpected-atom-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; lambda = ( "fn" / λ ) ws "(" *( ws pat ) ws ")" ws exp
  (define abs-lambda ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract a @('lambda') to
            an @(tsee atom) @(':lambda') or @(':lambdan')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A term lambda abstraction with one parameter becomes
       a unary term lambda abstraction @(':lambda');
       one with two or more parameters becomes
       an n-ary term lambda abstraction @(':lambdan')
       (see @(tsee atom))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "lambda"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf params) (abs-*-ws-pat sub.4th))
         ((okf body) (abs-exp body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-atom-lambda :param (car params) :body body :type? nil)
        (make-atom-lambdan :params params :body body :type? nil)))
    :measure (abnf::tree-count tree))

  ;; type-lambda = ( "t-fn" / "tλ" ) ws "(" *( ws type-var ) ws ")" ws exp
  (define abs-type-lambda ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract a @('type-lambda') to
            an @(tsee atom) @(':tlambda') or @(':tlambdan')."
    :long
    (xdoc::topstring
     (xdoc::p
      "A type lambda abstraction with one parameter becomes
       a unary type lambda abstraction @(':tlambda');
       one with two or more parameters becomes
       an n-ary type lambda abstraction @(':tlambdan')
       (see @(tsee atom))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "type-lambda"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf params) (abs-*-ws-type-var sub.4th))
         ((okf body) (abs-exp body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-atom-tlambda :param (car params) :body body)
        (make-atom-tlambdan :params params :body body)))
    :measure (abnf::tree-count tree))

  ;; ispace-lambda = ( "i-fn" / "iλ" ) ws "(" *( ws ispace-var ) ws ")" ws exp
  (define abs-ispace-lambda ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract an @('ispace-lambda') to
            an @(tsee atom) @(':ilambda') or @(':ilambdan')."
    :long
    (xdoc::topstring
     (xdoc::p
      "An ispace lambda abstraction with one parameter becomes
       a unary ispace lambda abstraction @(':ilambda');
       one with two or more parameters becomes
       an n-ary ispace lambda abstraction @(':ilambdan')
       (see @(tsee atom))."))
    (b* (((okf (abnf::tree-list-tuple8 sub))
          (abnf::check-tree-nonleaf-8 tree "ispace-lambda"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf params) (abs-*-ws-ispace-var sub.4th))
         ((okf body) (abs-exp body-tree)))
      (if (and (consp params)
               (endp (cdr params)))
          (make-atom-ilambda :param (car params) :body body)
        (make-atom-ilambdan :params params :body body)))
    :measure (abnf::tree-count tree))

  ;; box-expr = "box" ws "(" *( ws ispace ) ws ")" ws exp ws type
  (define abs-box-expr ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract a @('box-expr') to an @(tsee atom) @(':box')."
    (b* (((okf (abnf::tree-list-tuple10 sub))
          (abnf::check-tree-nonleaf-10 tree "box-expr"))
         ((okf e-tree) (abnf::check-tree-list-1 sub.8th))
         ((okf te-tree) (abnf::check-tree-list-1 sub.10th))
         ((okf ispaces) (abs-*-ws-ispace sub.4th))
         ((okf array) (abs-exp e-tree))
         ((okf ty) (abs-type te-tree)))
      (make-atom-box :ispaces ispaces :array array :type ty))
    :measure (abnf::tree-count tree))

  ;; ------------------------------------------------------------------
  ;; Bindings
  ;; ------------------------------------------------------------------

  ;; bind = "(" ws bind-body ws ")"
  (define abs-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('bind') to a @(tsee bind)."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "bind"))
         ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
      (abs-bind-body body-tree))
    :measure (abnf::tree-count tree))

  (define abs-bind-body ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('bind-body') to a @(tsee bind)."
    (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "bind-body"))
         ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
      (cond ((equal rulename? "val-bind") (abs-val-bind inner))
            ((equal rulename? "fun-bind") (abs-fun-bind inner))
            ((equal rulename? "tfun-bind") (abs-tfun-bind inner))
            ((equal rulename? "ifun-bind") (abs-ifun-bind inner))
            ((equal rulename? "type-bind") (abs-type-bind inner))
            ((equal rulename? "ispace-bind") (abs-ispace-bind inner))
            ((equal rulename? "at-fun-bind") (abs-at-fun-bind inner))
            (t (reserrf (list :unexpected-bind-body
                              (abnf::tree-info-for-error inner))))))
    :measure (abnf::tree-count tree))

  ;; val-bind = "val" ws id ws e                                      (alt 1)
  ;;          / "val" ws "(" ws val-typed-sig ws ")" ws e             (alt 2)
  (define abs-val-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('val-bind') to a @(tsee bind) @(':val')."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "val-bind")))
      (case (len treess)
        (5 (b* (((okf (abnf::tree-list-tuple5 sub))
                 (abnf::check-tree-list-list-5 treess))
                ((okf id-tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf e-tree) (abnf::check-tree-list-1 sub.5th))
                ((okf name) (abs-identifier id-tree))
                ((okf e) (abs-exp e-tree)))
             (make-bind-val :var name
                            :type? (type-option-none)
                            :expr e)))
        (9 (b* (((okf (abnf::tree-list-tuple9 sub))
                 (abnf::check-tree-list-list-9 treess))
                ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
                ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
                ((okf vt) (abs-val-typed-sig sig-tree))
                ((okf e) (abs-exp e-tree)))
             (make-bind-val :var (var+type?->var vt)
                            :type? (var+type?->type? vt)
                            :expr e)))
        (otherwise
         (reserrf (list :val-bind-shape (len treess))))))
    :measure (abnf::tree-count tree))

  ;; fun-bind = "fun" ws "(" ws fun-sig ws ")" ws exp
  (define abs-fun-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('fun-bind') to a @(tsee bind) @(':fun')."
    (b* (((okf (abnf::tree-list-tuple9 sub))
          (abnf::check-tree-nonleaf-9 tree "fun-bind"))
         ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
         ((okf info) (abs-fun-sig sig-tree))
         ((okf body) (abs-exp e-tree)))
      (make-bind-fun :var (fun-sig-info->name info)
                     :params (fun-sig-info->params info)
                     :type? (fun-sig-info->ret-type info)
                     :expr body))
    :measure (abnf::tree-count tree))

  ;; tfun-bind = "t-fun" ws "(" ws tfun-sig ws ")" ws exp
  (define abs-tfun-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('tfun-bind') to a @(tsee bind) @(':tfun')."
    (b* (((okf (abnf::tree-list-tuple9 sub))
          (abnf::check-tree-nonleaf-9 tree "tfun-bind"))
         ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
         ((okf info) (abs-tfun-sig sig-tree))
         ((okf body) (abs-exp e-tree)))
      (make-bind-tfun :var (tfun-sig-info->name info)
                      :params (tfun-sig-info->params info)
                      :type? (tfun-sig-info->ret-type info)
                      :expr body))
    :measure (abnf::tree-count tree))

  ;; ifun-bind = "i-fun" ws "(" ws ifun-sig ws ")" ws exp
  (define abs-ifun-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract an @('ifun-bind') to a @(tsee bind) @(':ifun')."
    (b* (((okf (abnf::tree-list-tuple9 sub))
          (abnf::check-tree-nonleaf-9 tree "ifun-bind"))
         ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
         ((okf info) (abs-ifun-sig sig-tree))
         ((okf body) (abs-exp e-tree)))
      (make-bind-ifun :var (ifun-sig-info->name info)
                      :params (ifun-sig-info->params info)
                      :type? (ifun-sig-info->ret-type info)
                      :expr body))
    :measure (abnf::tree-count tree))

  ;; at-fun-bind = "fun" ws "(" ws at-fun-sig ws ")" ws exp
  (define abs-at-fun-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract an @('at-fun-bind') to a @(tsee bind) @(':cfun')."
    (b* (((okf (abnf::tree-list-tuple9 sub))
          (abnf::check-tree-nonleaf-9 tree "at-fun-bind"))
         ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
         ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
         ((okf info) (abs-at-fun-sig sig-tree))
         ((okf body) (abs-exp e-tree)))
      (make-bind-cfun :var (at-fun-sig-info->name info)
                      :tparams? (at-fun-sig-info->tparams info)
                      :iparams? (at-fun-sig-info->iparams info)
                      :params (at-fun-sig-info->params info)
                      :type (at-fun-sig-info->ret-type info)
                      :expr body))
    :measure (abnf::tree-count tree))

  ;; ------------------------------------------------------------------
  ;; Repetition helpers (in cluster: each ultimately calls abs-exp,
  ;; abs-atom, or abs-bind, all of which are in the cluster).
  ;; ------------------------------------------------------------------

  (define abs-ws-exp ((tree abnf::treep))
    :returns (e expr-resultp)
    :short "Abstract a @('( ws exp )') wrapper to an @(tsee expr)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf e-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-exp e-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-exp ((trees abnf::tree-listp))
    :returns (es expr-list-resultp)
    :short "Abstract @('*( ws exp )') to an @(tsee expr-list)."
    (b* (((when (endp trees)) nil)
         ((okf e) (abs-ws-exp (car trees)))
         ((okf rest) (abs-*-ws-exp (cdr trees))))
      (cons e rest))
    :measure (abnf::tree-list-count trees))

  (define abs-ws-atom ((tree abnf::treep))
    :returns (a atom-resultp)
    :short "Abstract a @('( ws atom )') wrapper to an @(tsee atom)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf a-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-atom a-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-atom ((trees abnf::tree-listp))
    :returns (as atom-list-resultp)
    :short "Abstract @('*( ws atom )') to an @(tsee atom-list)."
    (b* (((when (endp trees)) nil)
         ((okf a) (abs-ws-atom (car trees)))
         ((okf rest) (abs-*-ws-atom (cdr trees))))
      (cons a rest))
    :measure (abnf::tree-list-count trees))

  (define abs-ws-bind ((tree abnf::treep))
    :returns (b bind-resultp)
    :short "Abstract a @('( ws bind )') wrapper to a @(tsee bind)."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree nil))
         ((okf b-tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-bind b-tree))
    :measure (abnf::tree-count tree))

  (define abs-*-ws-bind ((trees abnf::tree-listp))
    :returns (bs bind-list-resultp)
    :short "Abstract @('*( ws bind )') to a @(tsee bind-list)."
    (b* (((when (endp trees)) nil)
         ((okf b) (abs-ws-bind (car trees)))
         ((okf rest) (abs-*-ws-bind (cdr trees))))
      (cons b rest))
    :measure (abnf::tree-list-count trees))

  :ruler-extenders :all
  :verify-guards nil

  ///

  (verify-guards abs-exp)

  (fty::deffixequiv-mutual abs-exprs/atoms/binds))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Slice 6: top-level expression entry
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; top-exp = ws exp ws
(define abs-top-exp ((tree abnf::treep))
  :returns (e expr-resultp)
  :short "Abstract a @('top-exp') CST to an @(tsee expr) AST."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "top-exp"))
       ((okf e-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-exp e-tree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Slice 7: imports, declarations, and source files
;;
;; These come after the expression cluster because they reference
;; abs-bind, abs-exp, and abs-fun-sig, but nothing references them back,
;; so they are not mutually recursive with it.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; import = "(" ws "import" ws string-lit ws ")"
(define abs-import ((tree abnf::treep))
  :returns (imp import-resultp)
  :short "Abstract an @('import') to an @(tsee import)."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "import"))
       ((okf str-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf chars) (abs-string-lit str-tree)))
    (make-import :path chars)))

(define abs-ws-import ((tree abnf::treep))
  :returns (imp import-resultp)
  :short "Abstract a @('( ws import )') wrapper to an @(tsee import)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf i-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-import i-tree)))

(define abs-*-ws-import ((trees abnf::tree-listp))
  :returns (imps import-list-resultp)
  :short "Abstract @('*( ws import )') to an @(tsee import-list)."
  (b* (((when (endp trees)) nil)
       ((okf imp) (abs-ws-import (car trees)))
       ((okf rest) (abs-*-ws-import (cdr trees))))
    (cons imp rest)))

;; def-decl = "def" ws bind
(define abs-def-decl ((tree abnf::treep))
  :returns (d decl-resultp)
  :short "Abstract a @('def-decl') to a @(tsee decl) @(':def')."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "def-decl"))
       ((okf b-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf b) (abs-bind b-tree)))
    (make-decl-def :bind b)))

;; entry-decl = "entry" ws "(" ws fun-sig ws ")" ws exp
(define abs-entry-decl ((tree abnf::treep))
  :returns (d decl-resultp)
  :short "Abstract an @('entry-decl') to a @(tsee decl) @(':entry')."
  (b* (((okf (abnf::tree-list-tuple9 sub))
        (abnf::check-tree-nonleaf-9 tree "entry-decl"))
       ((okf sig-tree) (abnf::check-tree-list-1 sub.5th))
       ((okf e-tree) (abnf::check-tree-list-1 sub.9th))
       ((okf info) (abs-fun-sig sig-tree))
       ((okf body) (abs-exp e-tree)))
    (make-decl-entry :var (fun-sig-info->name info)
                     :params (fun-sig-info->params info)
                     :type? (fun-sig-info->ret-type info)
                     :expr body)))

(define abs-decl-body ((tree abnf::treep))
  :returns (d decl-resultp)
  :short "Abstract a @('decl-body') to a @(tsee decl)."
  (b* (((okf inner) (abnf::check-tree-nonleaf-1-1 tree "decl-body"))
       ((okf rulename?) (abnf::check-tree-nonleaf? inner)))
    (cond ((equal rulename? "def-decl") (abs-def-decl inner))
          ((equal rulename? "entry-decl") (abs-entry-decl inner))
          (t (reserrf (list :unexpected-decl-body
                            (abnf::tree-info-for-error inner)))))))

(define abs-decl ((tree abnf::treep))
  :returns (d decl-resultp)
  :short "Abstract a @('decl') to a @(tsee decl)."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "decl"))
       ((okf body-tree) (abnf::check-tree-list-1 sub.3rd)))
    (abs-decl-body body-tree)))

(define abs-ws-decl ((tree abnf::treep))
  :returns (d decl-resultp)
  :short "Abstract a @('( ws decl )') wrapper to a @(tsee decl)."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree nil))
       ((okf d-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-decl d-tree)))

(define abs-*-ws-decl ((trees abnf::tree-listp))
  :returns (ds decl-list-resultp)
  :short "Abstract @('*( ws decl )') to a @(tsee decl-list)."
  (b* (((when (endp trees)) nil)
       ((okf d) (abs-ws-decl (car trees)))
       ((okf rest) (abs-*-ws-decl (cdr trees))))
    (cons d rest)))

;; file = *( ws import ) *( ws decl ) ws
(define abs-file ((tree abnf::treep))
  :returns (f file-resultp
              :hints (("Goal" :in-theory (enable filep))))
  :short "Abstract a @('file') CST to a @(tsee file) AST."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "file"))
       ((okf imports) (abs-*-ws-import sub.1st))
       ((okf decls) (abs-*-ws-decl sub.2nd)))
    (make-file :imports imports :decls decls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
