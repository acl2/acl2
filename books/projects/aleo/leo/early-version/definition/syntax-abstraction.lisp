; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "grammar")
(include-book "files")

(include-book "kestrel/fty/character-result" :dir :system)
(include-book "kestrel/fty/character-list-result" :dir :system)
(include-book "kestrel/fty/integer-result" :dir :system)
(include-book "kestrel/fty/boolean-result" :dir :system)
(include-book "kestrel/fty/nat-natlist-result" :dir :system)
(include-book "kestrel/fty/nat-option-result" :dir :system)
(include-book "kestrel/fty/nat-option-list-result" :dir :system)
(include-book "kestrel/fty/natoption-natoptionlist-result" :dir :system)
(include-book "kestrel/fty/string-result" :dir :system)
(include-book "kestrel/fty/string-list-result" :dir :system)
(include-book "projects/abnf/tree-utilities" :dir :system)
(include-book "std/strings/letter-chars" :dir :system)
(include-book "std/strings/ucletter-chars" :dir :system)
(include-book "std/strings/lcletter-chars" :dir :system)
(include-book "std/strings/decimal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to string library

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled letter-char-p-alt-def
  (equal (str::letter-char-p x)
         (or (str::ucletter-char-p x)
             (str::lcletter-char-p x)))
  :enable (str::letter-char-p
           str::ucletter-char-p
           str::lcletter-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled letter/digit/uscore-char-p-alt-def
  (equal (str::letter/digit/uscore-char-p x)
         (or (str::letter-char-p x)
             (str::dec-digit-char-p x)
             (equal x #\_)))
  :enable (str::letter/digit/uscore-char-p
           str::letter-char-p
           str::dec-digit-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled lcletter/digit-char-p-alt-def
  (equal (str::lcletter/digit-char-p x)
         (or (str::lcletter-char-p x)
             (str::dec-digit-char-p x)))
  :enable (str::lcletter/digit-char-p
           str::lcletter-char-p
           str::dec-digit-char-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ syntax-abstraction
  :parents (abstract-syntax)
  :short "Mapping from concrete to abstract syntax, for Leo code."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " is an abstraction of the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ". Here we define the abstraction mapping from "
    (xdoc::seetopic "concrete-syntax-trees" "CSTs")
    " to "
    (xdoc::seetopic "abstract-syntax-trees" "ASTs")
    ".")
   (xdoc::p
    "For now our abstraction mapping has weak guards and many run-time checks.
     We plan to turn things around eventually,
     i.e. to have strong guards and ideally no run-time checks.
     This may involve the development of
     some more general support in our ABNF library for this."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-?-comma ((tree abnf::treep))
  :returns (pass abnf::pass-resultp)
  :short "Check if a tree is @('[ \",\" ]')."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
       ((when (endp treess)) :pass)
       ((okf trees) (abnf::check-tree-list-list-1 treess))
       ((okf tree) (abnf::check-tree-list-1 trees)))
    (abnf::check-tree-ichars tree ","))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-optional-equals-p ((tree abnf::treep))
  :returns (ret boolean-resultp)
  :short "Check if a tree is @('[ \"=\" ]')."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
       ((when (endp treess)) nil) ; empty optional tree
       ((okf trees) (abnf::check-tree-list-list-1 treess))
       ((okf tree) (abnf::check-tree-list-1 trees))
       (pass (abnf::check-tree-ichars tree "="))
       ((when (reserrp pass)) pass))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-literal-is-string-literal ((lit literalp))
  :returns (chars char-list-resultp)
  :short "Check if a literal is a string literal,
          returning its list of characters if successful."
  (case (literal-kind lit)
    (:string (literal-string->get lit))
    (t (reserrf (list :found (literal-fix lit)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-decimal-digit-to-nat ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract a @('decimal-digit') to a natural number."
  (b* (((okf nat) (abnf::check-tree-nonleaf-num-range tree "decimal-digit" #x30 #x39)))
    (- nat #x30))
  :hooks (:fix)
  ///

  (defret natp-of-decimal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret abs-decimal-digit-to-nat-bound
    (implies (not (reserrp nat))
             (< nat 10))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-decimal-digit-to-nat ((trees abnf::tree-listp))
  :returns (nat nat-resultp)
  :short "Abstract a @('*decimal-digit') to a natural number,
          interpreting the digits in big endian."
  (abs-*-decimal-digit-to-nat-aux trees 0)
  :hooks (:fix)

  :prepwork
  ((define abs-*-decimal-digit-to-nat-aux ((trees abnf::tree-listp)
                                           (current natp))
     :returns (nat nat-resultp)
     :parents nil
     (b* (((when (endp trees)) (nfix current))
          ((okf digit-nat) (abs-decimal-digit-to-nat (car trees))))
       (abs-*-decimal-digit-to-nat-aux (cdr trees)
                                       (+ digit-nat
                                          (* (nfix current) 10))))
     :hooks (:fix)))

  ///

  (defret natp-of-abs-*-decimal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-decimal-digit-to-char ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('decimal-digit') to an ACL2 character."
  (b* (((okf nat) (abnf::check-tree-nonleaf-num-range tree "decimal-digit" #x30 #x39)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret dec-digit-char-p-of-abs-decimal-digit-to-char
    (implies (not (reserrp char))
             (str::dec-digit-char-p char))
    :hints (("Goal" :in-theory (enable str::dec-digit-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-octal-digit-to-nat ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract an @('octal-digit') to a natural number."
  (b* (((okf nat) (abnf::check-tree-nonleaf-num-range tree "octal-digit" #x30 #x37)))
    (- nat #x30))
  :hooks (:fix)
  ///

  (defret natp-of-octal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret abs-octal-digit-to-nat-bound
    (implies (not (reserrp nat))
             (< nat 8))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-hexadecimal-digit-to-nat ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract a @('hexadecimal-digit') to a natural number."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "hexadecimal-digit"))
       (nat (abs-decimal-digit-to-nat tree))
       ((when (not (reserrp nat))) nat)
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-insensitive-chars-p nats (list #\a)) 10)
          ((abnf::nats-match-insensitive-chars-p nats (list #\b)) 11)
          ((abnf::nats-match-insensitive-chars-p nats (list #\c)) 12)
          ((abnf::nats-match-insensitive-chars-p nats (list #\d)) 13)
          ((abnf::nats-match-insensitive-chars-p nats (list #\e)) 14)
          ((abnf::nats-match-insensitive-chars-p nats (list #\f)) 15)
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix)
  ///

  (defret natp-of-hexadecimal-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining)

  (defret abs-hexadecimal-digit-to-nat-bound
    (implies (not (reserrp nat))
             (< nat 16))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-hexadecimal-digit-to-nat ((trees abnf::tree-listp))
  :returns (nat nat-resultp)
  :short "Abstract a @('*hexadecimal-digit') to a natural number,
          interpreting the digits in big endian."
  (abs-*-hexadecimal-digit-to-nat-aux trees 0)
  :hooks (:fix)

  :prepwork
  ((define abs-*-hexadecimal-digit-to-nat-aux ((trees abnf::tree-listp)
                                               (current natp))
     :returns (nat nat-resultp)
     :parents nil
     (b* (((when (endp trees)) (nfix current))
          ((okf digit-nat) (abs-hexadecimal-digit-to-nat (car trees))))
       (abs-*-hexadecimal-digit-to-nat-aux (cdr trees)
                                           (+ digit-nat
                                              (* (nfix current) 16))))
     :hooks (:fix)))

  ///

  (defret natp-of-abs-*-hexadecimal-digit-to-nat
    (implies (not (reserrp nat))
             (natp nat))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-uppercase-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract an @('uppercase-letter') to an ACL2 character."
  (b* (((okf nat)
        (abnf::check-tree-nonleaf-num-range tree "uppercase-letter" #x41 #x5a)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret ucletter-char-p-of-abs-uppercase-letter
    (implies (not (reserrp char))
             (str::ucletter-char-p char))
    :hints (("Goal" :in-theory (enable str::ucletter-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-lowercase-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('lowercase-letter') to an ACL2 character."
  (b* (((okf nat)
        (abnf::check-tree-nonleaf-num-range tree "lowercase-letter" #x61 #x7a)))
    (code-char nat))
  :hooks (:fix)
  ///

  (defret lcletter-char-p-of-abs-lowercase-letter
    (implies (not (reserrp char))
             (str::lcletter-char-p char))
    :hints (("Goal" :in-theory (enable str::lcletter-char-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-letter ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('letter') to an ACL2 character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "letter"))
       (char (abs-uppercase-letter tree))
       ((when (not (reserrp char))) char)
       (char (abs-lowercase-letter tree))
       ((when (not (reserrp char))) char))
    (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))
  :hooks (:fix)
  ///

  (defret letter-char-p-of-abs-letter
    (implies (not (reserrp char))
             (str::letter-char-p char))
    :hints (("Goal" :in-theory (enable letter-char-p-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-letter/decimaldigit/underscore ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('( letter / decimal-digit / \"_\" )')
          to an ACL2 character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree nil))
       (char (abs-letter tree))
       ((when (not (reserrp char))) char)
       (char (abs-decimal-digit-to-char tree))
       ((when (not (reserrp char))) char)
       (pass (abnf::check-tree-ichars tree "_"))
       ((when (not (reserrp pass))) #\_))
    (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))
  :hooks (:fix)
  ///

  (defret letter/digit/uscore-char-p-of-abs-letter/decimaldigit/underscore
    (implies (not (reserrp char))
             (str::letter/digit/uscore-char-p char))
    :hints (("Goal" :in-theory (enable
                                letter/digit/uscore-char-p-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-letter/decimaldigit/underscore ((trees abnf::tree-listp))
  :returns
  (chars
   character-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      acl2::characterp-when-character-resultp-and-not-reserrp
      acl2::character-listp-when-character-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( letter / digit / \"_\" )')
          to a list of ACL2 characters."
  (b* (((when (endp trees)) nil)
       ((okf char) (abs-letter/decimaldigit/underscore (car trees)))
       ((okf chars) (abs-*-letter/decimaldigit/underscore (cdr trees))))
    (cons char chars))
  :hooks (:fix)
  ///

  (defret letter/digit/uscore-char-listp-of-abs-*-letter/decimaldigit/underscore
    (implies (not (reserrp chars))
             (str::letter/digit/uscore-charlist-p chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-identifier ((tree abnf::treep))
  :returns (id identifier-resultp)
  :short "Abstract an @('identifier') to an identifier."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "identifier"))
       ((okf letter-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf char) (abs-letter letter-tree))
       ((okf chars) (abs-*-letter/decimaldigit/underscore sub.2nd))
       (string (str::implode (cons char chars)))
       ((when (member-equal string *keywords*))
        (reserrf (list :identifier-is-keyword string)))
       ((when (member-equal string (list "true" "false")))
        (reserrf (list :identifier-is-boolean-literal string)))
       ((when (prefixp (str::explode "aleo1") (str::explode string)))
        (reserrf (list :identifier-is-aleo1 string))))
    (identifier string))
  :guard-hints (("Goal" :in-theory (enable identifier-string-p
                                           identifier-grammar-chars-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-program-id ((tree abnf::treep))
  :returns (progid programid-resultp)
  :short "Abstract a @('program-id') to a @('programid')."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "program-id"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "."))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf network) (abs-identifier tree)))
    (make-programid :name name
                    :network network))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-locator ((tree abnf::treep))
  :returns (loc locator-resultp)
  :short "Abstract a @('locator') to a Leo locator."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "locator"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf program) (abs-program-id tree))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "/"))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf name) (abs-identifier tree)))
    (make-locator :program program
                  :name name))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-annotation ((tree abnf::treep))
  :returns (ann annotation-resultp)
  :short "Abstract an @('annotation') to an annotation."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "annotation"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "@"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf id) (abs-identifier tree)))
    (make-annotation :name id))
  :hooks (:fix))

(define abs-*-annotation ((trees abnf::tree-listp))
  :returns
  (anns annotation-list-resultp
        :hints
        (("Goal"
          :in-theory
          (enable
           annotationp-when-annotation-resultp-and-not-reserrp
           annotation-listp-when-annotation-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*annotation') to a list of annotations."
  (b* (((when (endp trees)) nil)
       ((okf ann) (abs-annotation (car trees)))
       ((okf anns) (abs-*-annotation (cdr trees))))
    (cons ann anns))
  :hooks (:fix)
  ///

  (defret annotation-listp-of-abs-*-annotation
    (implies (not (reserrp anns))
             (annotation-listp anns))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-lowercaseletter/decimaldigit ((tree abnf::treep))
  :returns (char character-resultp)
  :short "Abstract a @('( lowercase-letter / decimal-digit )')
          to an ACL2 character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree nil))
       (char (abs-lowercase-letter tree))
       ((when (not (reserrp char))) char)
       (char (abs-decimal-digit-to-char tree))
       ((when (not (reserrp char))) char))
    (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))
  :hooks (:fix)
  ///

  (defret loletter/digit-char-p-of-abs-lowercaseletter/decimaldigit
    (implies (not (reserrp char))
             (str::lcletter/digit-char-p char))
    :hints (("Goal" :in-theory (enable lcletter/digit-char-p-alt-def)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-lowercaseletter/decimaldigit ((trees abnf::tree-listp))
  :returns
  (chars
   character-list-resultp
   :hints
   (("Goal"
     :in-theory
     (enable
      acl2::characterp-when-character-resultp-and-not-reserrp
      acl2::character-listp-when-character-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( lowercase-letter / decimal-digit )')
          to a list of ACL2 characters."
  (b* (((when (endp trees)) nil)
       ((okf char) (abs-lowercaseletter/decimaldigit (car trees)))
       ((okf chars) (abs-*-lowercaseletter/decimaldigit (cdr trees))))
    (cons char chars))
  :hooks (:fix)
  ///

  (defret loletter/digit-char-listp-of-abs-*-lowercaseletter/decimaldigit
    (implies (not (reserrp chars))
             (str::lcletter/digit-charlist-p chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-numeral ((tree abnf::treep))
  :returns (nat nat-resultp)
  :short "Abstract a @('numeral') to a natural number."
  (b* (((okf sub) (abnf::check-tree-nonleaf-1 tree "numeral"))
       ((unless (consp sub)) (reserrf (list :empty-numeral))))
    (abs-*-decimal-digit-to-nat sub))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unsigned-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract an @('unsigned-literal') to an unsigned literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "unsigned-literal"))
       ((okf num-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf nat) (abs-numeral num-tree))
       ((okf type-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf type-tree) (abnf::check-tree-nonleaf-1-1 type-tree nil))
       ((okf nats) (abnf::check-tree-leafterm type-tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "u8"))
           (make-literal-unsigned :val nat :size (bitsize-8)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u16"))
           (make-literal-unsigned :val nat :size (bitsize-16)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u32"))
           (make-literal-unsigned :val nat :size (bitsize-32)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u64"))
           (make-literal-unsigned :val nat :size (bitsize-64)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u128"))
           (make-literal-unsigned :val nat :size (bitsize-128)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-signed-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('signed-literal') to a signed literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "signed-literal"))
       ((okf num-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf nat) (abs-numeral num-tree))
       ((okf type-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf type-tree) (abnf::check-tree-nonleaf-1-1 type-tree nil))
       ((okf nats) (abnf::check-tree-leafterm type-tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "i8"))
           (make-literal-signed :val nat :size (bitsize-8)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i16"))
           (make-literal-signed :val nat :size (bitsize-16)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i32"))
           (make-literal-signed :val nat :size (bitsize-32)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i64"))
           (make-literal-signed :val nat :size (bitsize-64)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i128"))
           (make-literal-signed :val nat :size (bitsize-128)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-field-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('field-literal') to a field literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "field-literal"))
       ((okf num-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf nat) (abs-numeral num-tree))
       ((okf field-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars field-tree "field")))
    (literal-field nat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-product-group-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('product-group-literal') to a product group literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "product-group-literal"))
       ((okf num-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf nat) (abs-numeral num-tree))
       ((okf group-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars group-tree "group")))
    (literal-group (group-literal-product nat)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-scalar-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('scalar-literal') to a scalar literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "scalar-literal"))
       ((okf num-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf nat) (abs-numeral num-tree))
       ((okf scalar-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars scalar-tree "scalar")))
    (literal-scalar nat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-boolean-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('boolean-literal') to a boolean literal."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "boolean-literal"))
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "true"))
           (literal-bool t))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "false"))
           (literal-bool nil))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-address-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract an @('address-literal') to an address literal."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "address-literal"))
       ((okf aleo1-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars aleo1-tree "aleo1"))
       ((okf chars) (abs-*-lowercaseletter/decimaldigit sub.2nd))
       ((unless (= (len chars) 58)) (reserrf (list :found chars)))
       (chars (append (str::explode "aleo1") chars)))
    (literal-address (address (str::implode chars))))
  :guard-hints (("Goal" :in-theory (enable address-string-p
                                           address-chars-p)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-double-quote ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('double-quote') to a Leo character."
  (b* (((okf &) (abnf::check-tree-nonleaf-num-seq tree "double-quote" (list #x22))))
    (char #x22))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-double-quote-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('double-quote-escape') to a Leo character."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "double-quote-escape"))
       ((okf backslash-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars backslash-tree "\\"))
       ((okf dquote-tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-double-quote dquote-tree))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-backslash-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('backslash-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "backslash-escape"))
       ((okf &) (abnf::check-tree-ichars tree "\\\\")))
    (char (char-code #\\)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-line-feed-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('line-feed-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "line-feed-escape"))
       ((okf &) (abnf::check-tree-schars tree "\\n")))
    (char 10))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-carriage-return-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('carriage-return-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "carriage-return-escape"))
       ((okf &) (abnf::check-tree-schars tree "\\r")))
    (char 13))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-horizontal-tab-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('horizontal-tab-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "horizontal-tab-escape"))
       ((okf &) (abnf::check-tree-schars tree "\\t")))
    (char 9))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-null-character-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('null-character-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "null-character-escape"))
       ((okf &) (abnf::check-tree-schars tree "\\0")))
    (char 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-simple-character-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('simple-character-escape') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "simple-character-escape"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "double-quote-escape")
           (abs-double-quote-escape tree))
          ((equal rulename? "backslash-escape")
           (abs-backslash-escape tree))
          ((equal rulename? "line-feed-escape")
           (abs-line-feed-escape tree))
          ((equal rulename? "carriage-return-escape")
           (abs-carriage-return-escape tree))
          ((equal rulename? "horizontal-tab-escape")
           (abs-horizontal-tab-escape tree))
          ((equal rulename? "null-character-escape")
           (abs-null-character-escape tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-ascii-character-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract an @('ascii-character-escape') to a Leo character."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "ascii-character-escape"))
       ((okf x-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars x-tree "\\x"))
       ((okf oct-tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf hi) (abs-octal-digit-to-nat oct-tree))
       ((okf hex-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf lo) (abs-hexadecimal-digit-to-nat hex-tree)))
    (char (+ (* 16 hi) lo)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unicode-character-escape ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('unicode-character-escape') to a Leo character."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "unicode-character-escape"))
       ((okf u-tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars u-tree "\\u{"))
       ((unless (and (<= 1 (len sub.2nd)) (<= (len sub.2nd) 6)))
        (reserrf (list :found-hex-digits (len sub.2nd))))
       ((okf nat) (abs-*-hexadecimal-digit-to-nat sub.2nd))
       ((unless (<= nat #x10ffff))
        (reserrf (list :bad-code-point nat)))
       ((okf cb-tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-schars cb-tree "}")))
    (char nat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-safe-nonascii ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('safe-nonascii') to a Leo character."
  (b* (((okf nat)
        (abnf::check-tree-nonleaf-num-range-4 tree
                                        "safe-nonascii"
                                        #x80 #x2029
                                        #x202f #x2065
                                        #x2070 #xd7ff
                                        #xe000 #x10ffff)))
    (char nat))
  :guard-hints (("Goal" :in-theory (enable abnf::check-tree-nonleaf-num-range-4
                                           abnf::check-tree-num-range-4))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-not-double-quote-or-backslash-or-line-feed-or-carriage-return ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('not-double-quote-or-backslash-or-line-feed-or-carriage-return') to a Leo character."
  (b* (((okf tree1) (abnf::check-tree-nonleaf-1-1 tree "not-double-quote-or-backslash-or-line-feed-or-carriage-return"))
       ((when (abnf::tree-case tree1 :nonleaf)) (abs-safe-nonascii tree1))
       ((okf nat)
        (abnf::check-tree-nonleaf-num-range-3 tree
                                        "not-double-quote-or-backslash-or-line-feed-or-carriage-return"
                                        #x0 #x21
                                        #x23 #x5b
                                        #x5d #x7f)))
    (char nat))
  :guard-hints (("Goal" :in-theory (enable abnf::check-tree-nonleaf-num-range-3
                                           abnf::check-tree-num-range-3)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-string-literal-element ((tree abnf::treep))
  :returns (char char-resultp)
  :short "Abstract a @('string-literal-element') to a Leo character."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "string-literal-element"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "not-double-quote-or-backslash-or-line-feed-or-carriage-return")
           (abs-not-double-quote-or-backslash-or-line-feed-or-carriage-return tree))
          ((equal rulename? "simple-character-escape")
           (abs-simple-character-escape tree))
          ((equal rulename? "ascii-character-escape")
           (abs-ascii-character-escape tree))
          ((equal rulename? "unicode-character-escape")
           (abs-unicode-character-escape tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-string-literal-element ((trees abnf::tree-listp))
  :returns (chars char-list-resultp
                  :hints
                  (("Goal"
                    :in-theory
                    (enable
                     charp-when-char-resultp-and-not-reserrp
                     char-listp-when-char-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*string-literal-element') to a list of Leo characters."
  (b* (((when (endp trees)) nil)
       ((okf char) (abs-string-literal-element (car trees)))
       ((okf chars) (abs-*-string-literal-element (cdr trees))))
    (cons char chars))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-string-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('string-literal') to a string literal."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "string-literal"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abs-double-quote tree))
       ((okf chars) (abs-*-string-literal-element sub.2nd))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abs-double-quote tree)))
    (literal-string chars))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-integer-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract an @('integer-literal') to an integer literal."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "integer-literal"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "unsigned-literal")
           (abs-unsigned-literal tree))
          ((equal rulename? "signed-literal")
           (abs-signed-literal tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-numeric-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('numeric-literal') to a numeric literal."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "numeric-literal"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "integer-literal")
           (abs-integer-literal tree))
          ((equal rulename? "field-literal")
           (abs-field-literal tree))
          ((equal rulename? "product-group-literal")
           (abs-product-group-literal tree))
          ((equal rulename? "scalar-literal")
           (abs-scalar-literal tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-atomic-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract an @('atomic-literal') to an atomic literal."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "atomic-literal"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "numeric-literal")
           (abs-numeric-literal tree))
          ((equal rulename? "boolean-literal")
           (abs-boolean-literal tree))
          ((equal rulename? "address-literal")
           (abs-address-literal tree))
          ((equal rulename? "string-literal")
           (abs-string-literal tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unsigned-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract an @('unsigned-type') to an unsigned type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "unsigned-type"))
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "u8"))
           (type-unsigned (bitsize-8)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u16"))
           (type-unsigned (bitsize-16)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u32"))
           (type-unsigned (bitsize-32)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u64"))
           (type-unsigned (bitsize-64)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "u128"))
           (type-unsigned (bitsize-128)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-signed-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('signed-type') to an signed type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "signed-type"))
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "i8"))
           (type-signed (bitsize-8)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i16"))
           (type-signed (bitsize-16)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i32"))
           (type-signed (bitsize-32)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i64"))
           (type-signed (bitsize-64)))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "i128"))
           (type-signed (bitsize-128)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-integer-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract an @('integer-type') to an integer type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "integer-type"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "unsigned-type") (abs-unsigned-type tree))
          ((equal rulename? "signed-type") (abs-signed-type tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-field-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('field-type') to the field type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "field-type"))
       ((okf &) (abnf::check-tree-schars tree "field")))
    (type-field))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-group-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('group-type') to the group type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "group-type"))
       ((okf &) (abnf::check-tree-schars tree "group")))
    (type-group))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-scalar-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('scalar-type') to the scalar type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "scalar-type"))
       ((okf &) (abnf::check-tree-schars tree "scalar")))
    (type-scalar))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-arithmetic-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract an @('arithmetic-type') to an arithmetic type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "arithmetic-type"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "integer-type") (abs-integer-type tree))
          ((equal rulename? "field-type") (abs-field-type tree))
          ((equal rulename? "group-type") (abs-group-type tree))
          ((equal rulename? "scalar-type") (abs-scalar-type tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-boolean-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('boolean-type') to the boolean type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "boolean-type"))
       ((okf &) (abnf::check-tree-schars tree "bool")))
    (type-bool))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-address-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract an @('address-type') to the address type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "address-type"))
       ((okf &) (abnf::check-tree-schars tree "address")))
    (type-address))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-string-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('string-type') to the string type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "string-type"))
       ((okf &) (abnf::check-tree-schars tree "string")))
    (type-string))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-named-primitive-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('named-primitive-type') to a type."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "named-primitive-type"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "boolean-type") (abs-boolean-type tree))
          ((equal rulename? "arithmetic-type") (abs-arithmetic-type tree))
          ((equal rulename? "address-type") (abs-address-type tree))
          ((equal rulename? "string-type") (abs-string-type tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unit-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('unit-type') to a type."

  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "unit-type"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "("))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree ")")))
    (type-unit))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; named-type = named-primitive-type
;;            / identifier [ "." %s"record" ]
;;            / locator [ "." %s"record" ]
;;
(define abs-named-type ((tree abnf::treep))
  :returns (type type-resultp)
  :short "Abstract a @('named-type') to a type."
  (b* ((prim-type
        ;; If just one subtree, it is a named-primitive-type
        (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "named-type"))
             ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
          (cond ((equal rulename? "named-primitive-type")
                 (abs-named-primitive-type tree))
                (t (reserrf (list :found-subtree-1
                                  (abnf::tree-info-for-error tree)))))))
       ((when (not (reserrp prim-type)))
        prim-type)
       ;; internal and external types have two subtrees
       ((okf (abnf::tree-list-tuple2 named-type-subtrees))
        (abnf::check-tree-nonleaf-2 tree "named-type"))

;        (okf named-type-subtrees) (abnf::check-tree-nonleaf-2 tree "named-type"))

       ((okf id-or-loc-subtree) (abnf::check-tree-list-1 named-type-subtrees.1st))


       ((okf id-or-loc-rulename?) (abnf::check-tree-nonleaf? id-or-loc-subtree))
;                                   named-type-subtrees.1st))

       ((unless (member-equal id-or-loc-rulename?
                              '("identifier" "locator")))
        (reserrf (list :found-subtree-2 (abnf::tree-info-for-error tree))))

       ;; if dot-record? is T, we see ["." "record"]
       ;; if dot-record? is NIL, we see an empty optional item
       ;; if dot-record? is reserrp, we see neither of those
       ((okf dot-record?)
        (b* (((okf maybe-dot-record-subtree)
              (abnf::check-tree-list-1 named-type-subtrees.2nd))

             ((okf treess) (abnf::check-tree-nonleaf maybe-dot-record-subtree
                                               nil))
             ((when (endp treess)) nil) ; empty optional item
             ;; At this point, treess should have 2 items.
             ;; Let's destructure them (rebinding treess):
             ((okf (abnf::tree-list-tuple2 treess))
              (abnf::check-tree-nonleaf-2 maybe-dot-record-subtree nil))

             ((okf dot-tree) (abnf::check-tree-list-1 treess.1st))
             ((okf &) (abnf::check-tree-ichars dot-tree "."))
             ((okf record-tree) (abnf::check-tree-list-1 treess.2nd))
             ((okf &) (abnf::check-tree-schars record-tree "record")))
          t)))

    (cond ((equal id-or-loc-rulename? "identifier")
           (b* (((okf id) (abs-identifier id-or-loc-subtree)))
             (make-type-internal-named :get id :recordp dot-record?)))

          ((equal id-or-loc-rulename? "locator")
           (b* (((okf loc) (abs-locator id-or-loc-subtree)))
             (make-type-external-named :get loc :recordp dot-record?)))

          (t
           (reserrf (list :found-subtree-3 (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-types

  (define abs-comma-type ((tree abnf::treep))
    :returns (ret-type type-resultp)
    :short "Abstract a @('( \",\" type )') to a type."
    (b* (((okf (abnf::tree-list-tuple2 sub)) (abnf::check-tree-nonleaf-2 tree nil))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree ","))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-type tree))
    :measure (abnf::tree-count tree))

  (define abs-*-comma-type ((trees abnf::tree-listp))
    :returns (ret-types type-list-resultp)
    :short "Abstract @('*( \",\" type )') to a list of types."
    (b* (((when (endp trees)) nil)
         ((okf type) (abs-comma-type (car trees)))
         ((okf types) (abs-*-comma-type (cdr trees))))
      (cons type types))
    :measure (abnf::tree-list-count trees))

  (define abs-1*-comma-type ((trees abnf::tree-listp))
    :returns (ret-types type-list-resultp)
    :short
    "Abstract @('1*( \",\" type )') to a list of types."
    (b* (((when (endp trees))
          (reserrf (list :not-enough-types)))
         ((okf type) (abs-comma-type (car trees)))
         ((okf types) (abs-*-comma-type (cdr trees))))
      (cons type types))
    :measure (abnf::tree-list-count trees))

  (define abs-tuple-type ((tree abnf::treep))
    :returns (ret-type type-resultp)
    :short "Abstract a @('tuple-type') to a tuple type."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "tuple-type"))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree "("))

         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf type) (abs-type tree))

         ((okf types) (abs-1*-comma-type sub.3rd))

         ((okf tree) (abnf::check-tree-list-1 sub.4th))
         ((okf &) (check-?-comma tree))

         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf &) (abnf::check-tree-ichars tree ")")))

      (make-type-tuple :components (cons type types)))
    :measure (abnf::tree-count tree))

  (define abs-type ((tree abnf::treep))
    :returns (ret-type type-resultp)
    :short "Abstract a @('type') to a type."
    (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "type"))
         ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
      (cond
       ((equal rulename? "unit-type") (abs-unit-type tree))
       ((equal rulename? "named-type") (abs-named-type tree))
       ((equal rulename? "tuple-type") (abs-tuple-type tree))
       (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  :prepwork
  ((local
    (in-theory (enable typep-when-type-resultp-and-not-reserrp
                       type-listp-when-type-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards abs-type)

  (fty::deffixequiv-mutual abs-types))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-group-coordinate ((tree abnf::treep))
  :returns (coor coordinate-resultp)
  :short "Abstract a @('group-coordinate') to a group literal coordinate."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "group-coordinate")))
    (if (abnf::tree-case tree :nonleaf)
        (b* (((okf (abnf::tree-list-tuple2 sub))
              (abnf::check-tree-nonleaf-2 tree nil))
             ((okf num-tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nat) (abs-numeral num-tree))
             ((okf opt-dash-tree) (abnf::check-tree-list-1 sub.1st))
             ((okf opt-dash-sub) (abnf::check-tree-nonleaf opt-dash-tree nil))
             ((when (endp opt-dash-sub)) (coordinate-explicit nat))
             ((okf dash-trees) (abnf::check-tree-list-list-1 opt-dash-sub))
             ((okf dash-tree) (abnf::check-tree-list-1 dash-trees))
             ((okf &) (abnf::check-tree-ichars dash-tree "-")))
          (coordinate-explicit (- nat)))
      (b* (((okf nats) (abnf::check-tree-leafterm tree)))
        (cond ((abnf::nats-match-insensitive-chars-p nats (list #\+))
               (coordinate-sign-high))
              ((abnf::nats-match-insensitive-chars-p nats (list #\-))
               (coordinate-sign-low))
              ((abnf::nats-match-insensitive-chars-p nats (list #\_))
               (coordinate-inferred))
              (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-affine-group-literal ((tree abnf::treep))
  :returns (lit group-literal-resultp)
  :short "Abstract an @('affine-group-literal') to an affine group literal."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "affine-group-literal"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "("))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf x) (abs-group-coordinate tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ","))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf y) (abs-group-coordinate tree))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-ichars tree ")group")))
    (make-group-literal-affine :x x :y y))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-literal ((tree abnf::treep))
  :returns (lit literal-resultp)
  :short "Abstract a @('literal') to a literal."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "literal"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "atomic-literal")
           (abs-atomic-literal tree))
          ((equal rulename? "affine-group-literal")
           (b* (((okf glit) (abs-affine-group-literal tree)))
             (literal-group glit)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-variable-or-free-constant ((tree abnf::treep))
  :returns (ret-id identifier-resultp)
  :short "Abstract a @('variable-or-free-constant') to an identifier."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "variable-or-free-constant"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "identifier")
           (b* (((okf id) (abs-identifier tree)))
             id))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *unary-opcall-name-to-unop*
  :short "Unary operator call to unop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is an alist that maps a unary operator call's identifier name
     to the unop that is used for it in the abstract syntax."))
  `(("not" . ,(unop-not))  ; prefix is "!"
    ("neg" . ,(unop-neg))  ; prefix is "~"
     ; no prefix form:
    ("abs" . ,(unop-abs))
    ("abs_wrapped" . ,(unop-abs-wrapped))
    ("double" . ,(unop-double))
    ("inv" . ,(unop-inv))
    ("square_root" . ,(unop-square-root))
    ("square" . ,(unop-square))
    ))

(define unop-for-opcall-name ((name stringp))
  :returns (retval unop-resultp)
  :short "Accessor function for @('*unary-opcall-name-to-unop*')."
  (let ((unop? (cdr (assoc-equal name *unary-opcall-name-to-unop*))))
    (if (not (unopp unop?))
        (reserrf (list :unknown-unary-operator-name name))
      unop?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *binary-opcall-name-to-binop*
  :short "Binary operator call to binop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is an alist that maps a binary operator call's identifier name
     to the binop that is used for it in the abstract syntax.")
   (xdoc::p
    "The key-value pairs are listed in the order the @(see binop) alternatives
     are defined."))
  ;; Note, for the binop alternatives that do not have an operator-call syntax,
  ;; we add a comment to that effect.
  `(;; (binop-and) is for "&&", which does not have an operator-call syntax
    ;; (binop-or) is for "||", which does not have an operator-call syntax
    ("eq" . ,(binop-eq)) ; infix is "=='
    ("neq" . ,(binop-ne)) ; infix is "!="
    ("gte" . ,(binop-ge)) ; infix is ">="
    ("gt" . ,(binop-gt)) ; infix is ">"
    ("lte" . ,(binop-le)) ; infix is "<="
    ("lt" . ,(binop-lt)) ; infix is "<"
    ("xor" . ,(binop-bitxor)) ; infix is "^"
    ("or" . ,(binop-bitior)) ; infix is "|"
    ("and" . ,(binop-bitand)) ; infix is "&"
    ("shl" . ,(binop-shl)) ; infix is "<<"
    ("shr" . ,(binop-shr)) ; infix is ">>"
    ("add" . ,(binop-add)) ; infix is "+"
    ("sub" . ,(binop-sub)) ; infix is "-"
    ("mul" . ,(binop-mul)) ; infix is "*"
    ("div" . ,(binop-div)) ; infix is "/"
    ("rem" . ,(binop-rem)) ; infix is "%"
    ("pow" . ,(binop-pow)) ; infix is "**"
    ;; These have only operator call syntax
    ("nand" . ,(binop-nand))
    ("nor" . ,(binop-nor))
    ("shl_wrapped" . ,(binop-shl-wrapped))
    ("shr_wrapped" . ,(binop-shr-wrapped))
    ("add_wrapped" . ,(binop-add-wrapped))
    ("sub_wrapped" . ,(binop-sub-wrapped))
    ("mul_wrapped" . ,(binop-mul-wrapped))
    ("div_wrapped" . ,(binop-div-wrapped))
    ("rem_wrapped" . ,(binop-rem-wrapped))
    ("pow_wrapped" . ,(binop-pow-wrapped))
    ))

(define binop-for-opcall-name ((name stringp))
  :returns (retval binop-resultp)
  :short "Accessor function for @('*binary-opcall-name-to-binop*')."
  (let ((binop? (cdr (assoc-equal name *binary-opcall-name-to-binop*))))
    (if (not (binopp binop?))
        (reserrf (list :unknown-binary-operator-name name))
      binop?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-unit-expression ((tree abnf::treep))
  :returns (expression expression-resultp)
  :short "Abstract a @('unit-expression') to a expression."

  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "unit-expression"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "("))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree ")")))
    (expression-unit))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-expressions

  (define abs-primary-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('primary-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "primary-expression")))
      (if (and (consp treess)
               (endp (cdr treess)))
          (b* (((okf tree) (abnf::check-tree-list-1 (car treess)))
               (ident (abs-variable-or-free-constant tree))
               ((when (not (reserrp ident))) (expression-var/const ident))
               (lit (abs-literal tree))
               ((when (not (reserrp lit))) (expression-literal lit))
               (call (abs-free-function-call tree))
               ((when (not (reserrp call))) call)
               (unit (abs-unit-expression tree))
               ((when (not (reserrp unit))) unit)

               (tuple (abs-tuple-expression tree))
               ((when (not (reserrp tuple))) tuple)
               (struct (abs-struct-expression tree))
               ((when (not (reserrp struct))) struct))
            (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf &) (abnf::check-tree-ichars tree "("))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf expr) (abs-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf &) (abnf::check-tree-ichars tree ")")))
          expr)))
    :measure (abnf::tree-count tree))

  (define abs-struct-component-initializer ((tree abnf::treep))
    :returns (ci struct-init-resultp)
    :short "Abstract a @('struct-component-initializer') to a @('struct-init')."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree
                                          "struct-component-initializer")))
      ;; There is either 1 thing or 3 things
      (if (and (consp treess)
               (endp (cdr treess)))
          (b* (((okf tree) (abnf::check-tree-list-1 (car treess)))
               ((okf id) (abs-identifier tree)))
            (make-struct-init :name id
                               :expr (expression-var/const id)))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf id) (abs-identifier tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree ":"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf expr) (abs-expression tree)))
          (make-struct-init :name id
                             :expr expr))))
      :measure (abnf::tree-count tree))

  (define abs-comma-struct-component-initializer ((tree abnf::treep))
    :returns (ci struct-init-resultp)
    :short "Abstract a @('\",\" struct-component-initializer') to a @('struct-init')."
    (b* (((okf (abnf::tree-list-tuple2 sub)) (abnf::check-tree-nonleaf-2 tree nil))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree ","))

         ((okf tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-struct-component-initializer tree))
    :measure (abnf::tree-count tree))

  ;; This should work like abs-*-comma-expression
  (define abs-*-comma-struct-component-initializer ((trees abnf::tree-listp))
    :returns (ccis struct-init-list-resultp)
    :short "Abstract a @('*( \",\" struct-component-initializer )')
            to a @('struct-init-list')."
    (b* (((when (endp trees)) nil)
         ((okf cci) (abs-comma-struct-component-initializer (car trees)))
         ((okf ccis) (abs-*-comma-struct-component-initializer (cdr trees))))
      (cons cci ccis))
    :measure (abnf::tree-list-count trees))

  (define abs-struct-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('struct-expression') to an expression."
    (b* (((okf (abnf::tree-list-tuple6 sub))
          (abnf::check-tree-nonleaf-6 tree "struct-expression"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf id) (abs-identifier tree))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf &) (abnf::check-tree-ichars tree "{"))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf cci) (abs-struct-component-initializer tree))
         ((okf ccis) (abs-*-comma-struct-component-initializer sub.4th))
         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf &) (check-?-comma tree))
         ((okf tree) (abnf::check-tree-list-1 sub.6th))
         ((okf &) (abnf::check-tree-ichars tree "}")))
      (make-expression-struct :type id :components (cons cci ccis)))
    :measure (abnf::tree-count tree))

  (define abs-1*-comma-expression ((trees abnf::tree-listp))
    :returns (ret-expressions expression-list-resultp)
    :short
    "Abstract @('1*( \",\" expression )') to a list of expressions."
    (b* (((when (endp trees))
          (reserrf (list :not-enough-expressions)))
         ((okf expression) (abs-comma-expression (car trees)))
         ((okf expressions) (abs-*-comma-expression (cdr trees))))
      (cons expression expressions))
    :measure (abnf::tree-list-count trees))

  (define abs-tuple-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('tuple-expression') to an expression."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "tuple-expression"))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree "("))

         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf expression) (abs-expression tree))

         ((okf expressions) (abs-1*-comma-expression sub.3rd))

         ((okf tree) (abnf::check-tree-list-1 sub.4th))
         ((okf &) (check-?-comma tree))

         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf &) (abnf::check-tree-ichars tree ")")))
      (make-expression-tuple :components (cons expression expressions)))
    :measure (abnf::tree-count tree))

  (define abs-postfix-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('postfix-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "postfix-expression")))
      (if (and (consp treess)
               (endp (cdr treess)))
          (b* (((okf tree) (abnf::check-tree-list-1 (car treess)))
               (e (abs-primary-expression tree))
               ((when (not (reserrp e))) e)
               (ccexpr (abs-struct-component-expression tree))
               ((when (not (reserrp ccexpr))) ccexpr)
               (tcexpr (abs-tuple-component-expression tree))
               ((when (not (reserrp tcexpr))) tcexpr)
               (opcall (abs-operator-call tree))
               ((when (not (reserrp opcall))) opcall))
            (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))
        (reserrf (list :wrong-number-of-branches (abnf::tree-info-for-error tree)))))
    :measure (abnf::tree-count tree))

  (define abs-struct-component-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('struct-component-expression') to an expression."
    (b* (((okf (abnf::tree-list-tuple3 sub))
          (abnf::check-tree-nonleaf-3 tree "struct-component-expression"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf e) (abs-postfix-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf &) (abnf::check-tree-ichars tree "."))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf id) (abs-identifier tree)))
      (make-expression-struct-component :struct e :component id))
    :measure (abnf::tree-count tree))

  (define abs-tuple-component-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('tuple-component-expression') to an expression."
    (b* (((okf (abnf::tree-list-tuple3 sub))
          (abnf::check-tree-nonleaf-3 tree "tuple-component-expression"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf e) (abs-postfix-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf &) (abnf::check-tree-ichars tree "."))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf n) (abs-numeral tree)))
      (make-expression-tuple-component :tuple e :index n))
    :measure (abnf::tree-count tree))

  ;; operator-call = unary-operator-call / binary-operator-call
  (define abs-operator-call ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('operator-call') to an expression."
    (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "operator-call"))
         ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
      (cond ((equal rulename? "unary-operator-call")
             (abs-unary-operator-call tree))
            ((equal rulename? "binary-operator-call")
             (abs-binary-operator-call tree))
            (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  ;; unary-operator-call = postfix-expression "." identifier "(" ")"
  (define abs-unary-operator-call ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('unary-operator-call') to an expression."
    (b* (((okf (abnf::tree-list-tuple5 sub))
          (abnf::check-tree-nonleaf-5 tree "unary-operator-call"))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf arg) (abs-postfix-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf &) (abnf::check-tree-ichars tree "."))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf id) (abs-identifier tree))
         ((okf tree) (abnf::check-tree-list-1 sub.4th))
         ((okf &) (abnf::check-tree-ichars tree "("))
         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf &) (abnf::check-tree-ichars tree ")"))
         ;; Done checking CST.  Now check unop.
         (unop (unop-for-opcall-name (identifier->name id)))
         ((when (reserrp unop))
          unop)) ; pass the error object up
      (make-expression-unary :op unop
                             :arg arg))
    :measure (abnf::tree-count tree))

  ;; binary-operator-call = postfix-expression "." identifier "(" expression [ "," ] ")"
  (define abs-binary-operator-call ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('binary-operator-call') to an expression."

    (b* (((okf (abnf::tree-list-tuple7 sub))
          (abnf::check-tree-nonleaf-7 tree "binary-operator-call"))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf arg) (abs-postfix-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf &) (abnf::check-tree-ichars tree "."))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf id) (abs-identifier tree))
         ((okf tree) (abnf::check-tree-list-1 sub.4th))
         ((okf &) (abnf::check-tree-ichars tree "("))
         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf arg2) (abs-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.6th))
         ((okf ?) (check-?-comma tree))
         ((okf tree) (abnf::check-tree-list-1 sub.7th))
         ((okf &) (abnf::check-tree-ichars tree ")"))

         ;; Done checking CST.  Now check unop.
         (binop (binop-for-opcall-name (identifier->name id)))
         ((when (reserrp binop))
          binop)) ; pass the error object up
      (make-expression-binary :op binop
                              :arg1 arg
                              :arg2 arg2))
    :measure (abnf::tree-count tree))

  (define abs-comma-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('( \",\" expression )') to an expression."
    (b* (((okf (abnf::tree-list-tuple2 sub)) (abnf::check-tree-nonleaf-2 tree nil))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree ","))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd)))
      (abs-expression tree))
    :measure (abnf::tree-count tree))

  (define abs-*-comma-expression ((trees abnf::tree-listp))
    :returns (exprs expression-list-resultp)
    :short "Abstract a @('*( \",\" expression )') to a list of expressions."
    (b* (((when (endp trees)) nil)
         ((okf expr) (abs-comma-expression (car trees)))
         ((okf exprs) (abs-*-comma-expression (cdr trees))))
      (cons expr exprs))
    :measure (abnf::tree-list-count trees))

  (define abs-?-expression-*-comma-expression-?-comma ((tree abnf::treep))
    :returns (exprs expression-list-resultp)
    :short "Abstract a @('[ expression *( \",\" expression ) [ \",\" ] ]')
            to a list of expressions."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
         ((when (endp treess)) nil)
         ((okf (abnf::tree-list-tuple3 sub)) (abnf::check-tree-list-list-3 treess))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf expr) (abs-expression tree))
         ((okf exprs) (abs-*-comma-expression sub.2nd))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf &) (check-?-comma tree)))
      (cons expr exprs))
    :measure (abnf::tree-count tree))

  (define abs-function-arguments ((tree abnf::treep))
    :returns (exprs expression-list-resultp)
    :short "Abstract a @('function-arguments') to a list of expressions."
    (b* (((okf (abnf::tree-list-tuple3 sub))
          (abnf::check-tree-nonleaf-3 tree "function-arguments"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree "("))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf exprs) (abs-?-expression-*-comma-expression-?-comma tree))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf &) (abnf::check-tree-ichars tree ")")))
      exprs)
    :measure (abnf::tree-count tree))

  (define abs-free-function-call ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('free-function-call') to an expression."
    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree "free-function-call"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ;; abstract either an identifier or a locator.  Order is irrelevant.
         (id (abs-identifier tree))
         ((okf id-or-loc) (if (reserrp id)
                              (abs-locator tree)
                            id))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf exprs) (abs-function-arguments tree)))
      (if (identifierp id-or-loc)
          (make-expression-internal-call :fun id-or-loc :args exprs)
        (make-expression-external-call :fun id-or-loc :args exprs)))
    :measure (abnf::tree-count tree))

  (define abs-unary-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('unary-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "unary-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-postfix-expression tree))
        (b* (((okf (abnf::tree-list-tuple2 sub))
              (abnf::check-tree-list-list-2 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf expr) (abs-unary-expression tree)))
          (cond ((abnf::nats-match-insensitive-chars-p nats (list #\!))
                 (make-expression-unary :op (unop-not)
                                        :arg expr))
                ((abnf::nats-match-insensitive-chars-p nats (list #\-))
                 (make-expression-unary :op (unop-neg)
                                        :arg expr))
                (t (reserrf (list :found-unary-operator nats)))))))
    :measure (abnf::tree-count tree))

  (define abs-exponential-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('exponential-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "exponential-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-unary-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-unary-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "**"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-exponential-expression tree)))
          (make-expression-binary :op (binop-pow)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-multiplicative-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('multiplicative-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "multiplicative-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-exponential-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-multiplicative-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf op)
              (cond ((abnf::nats-match-insensitive-chars-p nats (list #\*))
                     (binop-mul))
                    ((abnf::nats-match-insensitive-chars-p nats (list #\/))
                     (binop-div))
                    ((abnf::nats-match-insensitive-chars-p nats (list #\%))
                     (binop-rem))
                    (t (reserrf (list :found-binary-operator nats)))))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-exponential-expression tree)))
          (make-expression-binary :op op
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-additive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('additive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "additive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-multiplicative-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-additive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf op)
              (cond ((abnf::nats-match-insensitive-chars-p nats (list #\+))
                     (binop-add))
                    ((abnf::nats-match-insensitive-chars-p nats (list #\-))
                     (binop-sub))
                    (t (reserrf (list :found-binary-operator nats)))))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-multiplicative-expression tree)))
          (make-expression-binary :op op
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-shift-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('shift-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "shift-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-additive-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-shift-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf op)
              (cond ((abnf::nats-match-insensitive-chars-p nats (list #\< #\<))
                     (binop-shl))
                    ((abnf::nats-match-insensitive-chars-p nats (list #\> #\>))
                     (binop-shr))
                    (t (reserrf (list :found-binary-operator nats)))))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-additive-expression tree)))
          (make-expression-binary :op op
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-conjunctive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('conjunctive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "conjunctive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-shift-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-conjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "&"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-shift-expression tree)))
          (make-expression-binary :op (binop-bitand)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-disjunctive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('disjunctive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "disjunctive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-conjunctive-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-disjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "|"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-conjunctive-expression tree)))
          (make-expression-binary :op (binop-bitior)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-exclusive-disjunctive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('exclusive-disjunctive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "exclusive-disjunctive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-disjunctive-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-exclusive-disjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "^"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-disjunctive-expression tree)))
          (make-expression-binary :op (binop-bitxor)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-ordering-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('ordering-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "ordering-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-exclusive-disjunctive-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-exclusive-disjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf op)
              (cond ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\<))
                     (binop-lt))
                    ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\>))
                     (binop-gt))
                    ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\< #\=))
                     (binop-le))
                    ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\> #\=))
                     (binop-ge))
                    (t (reserrf (list :found-binary-operator nats)))))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-exclusive-disjunctive-expression tree)))
          (make-expression-binary :op op
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-equality-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('equality-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "equality-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-ordering-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-ordering-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf nats) (abnf::check-tree-leafterm tree))
             ((okf op)
              (cond ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\= #\=))
                     (binop-eq))
                    ((abnf::nats-match-insensitive-chars-p nats
                                                           (list #\! #\=))
                     (binop-ne))
                    (t (reserrf (list :found-binary-operator nats)))))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-ordering-expression tree)))
          (make-expression-binary :op op
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-conditional-conjunctive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('conditional-conjunctive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "conditional-conjunctive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-equality-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-conditional-conjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "&&"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-equality-expression tree)))
          (make-expression-binary :op (binop-and)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-conditional-disjunctive-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('conditional-disjunctive-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "conditional-disjunctive-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-conditional-conjunctive-expression tree))
        (b* (((okf (abnf::tree-list-tuple3 sub))
              (abnf::check-tree-list-list-3 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf left) (abs-conditional-disjunctive-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "||"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf right) (abs-conditional-conjunctive-expression tree)))
          (make-expression-binary :op (binop-or)
                                  :arg1 left
                                  :arg2 right))))
    :measure (abnf::tree-count tree))

  (define abs-binary-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('binary-expression') to an expression."
    (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "binary-expression")))
      (abs-conditional-disjunctive-expression tree))
    :measure (abnf::tree-count tree))

  (define abs-conditional-ternary-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract a @('conditional-ternary-expression') to an expression."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "conditional-ternary-expression")))
      (if (= (len treess) 1)
          (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
               ((okf tree) (abnf::check-tree-list-1 trees)))
            (abs-binary-expression tree))
        (b* (((okf (abnf::tree-list-tuple5 sub))
              (abnf::check-tree-list-list-5 treess))
             ((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf test) (abs-binary-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.2nd))
             ((okf &) (abnf::check-tree-ichars tree "?"))
             ((okf tree) (abnf::check-tree-list-1 sub.3rd))
             ((okf then) (abs-expression tree))
             ((okf tree) (abnf::check-tree-list-1 sub.4th))
             ((okf &) (abnf::check-tree-ichars tree ":"))
             ((okf tree) (abnf::check-tree-list-1 sub.5th))
             ((okf else) (abs-expression tree)))
          (make-expression-cond :test test
                                :then then
                                :else else))))
    :measure (abnf::tree-count tree))

  (define abs-expression ((tree abnf::treep))
    :returns (expr expression-resultp)
    :short "Abstract an @('expression') to an expression."
    (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "expression")))
      (abs-conditional-ternary-expression tree))
    :measure (abnf::tree-count tree))

  :ruler-extenders :all

  :prepwork
  ((local
    (in-theory
     (enable
      struct-initp-when-struct-init-resultp-and-not-reserrp
      struct-init-listp-when-struct-init-list-resultp-and-not-reserrp
      expressionp-when-expression-resultp-and-not-reserrp
      expression-listp-when-expression-list-resultp-and-not-reserrp
      abnf::tree-list-listp-when-tree-list-list-resultp-and-not-reserrp))))

  :verify-guards nil ; done below
  ///
  (verify-guards abs-expression)

  (fty::deffixequiv-mutual abs-expressions))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-return-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract a @('return-statement') to a statement."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "return-statement"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "return"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf expr) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (statement-return expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-variable-declaration ((tree abnf::treep))
  :returns (var vardecl-resultp)
  :short "Abstract a @('variable-declaration') to a variable declaration."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "variable-declaration"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "let"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf id) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ":"))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf type) (abs-type tree))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-ichars tree "="))
       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf expr) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (make-vardecl :name id :type type :init expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-constant-declaration ((tree abnf::treep))
  :returns (const constdecl-resultp)
  :short "Abstract a @('constant-declaration') to a constant declaration."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "constant-declaration"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "const"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf id) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ":"))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf type) (abs-type tree))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-ichars tree "="))
       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf expr) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (make-constdecl :name id :type type :init expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-assignment-operator ((tree abnf::treep))
  :returns (op asgop-resultp)
  :short "Abstract an @('assignment-operator') to an assignment operator."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "assignment-operator"))
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-insensitive-chars-p nats (list #\=))
           (asgop-asg))
          ;; arithmetic
          ((abnf::nats-match-insensitive-chars-p nats (list #\+ #\=))
           (asgop-asg-add))
          ((abnf::nats-match-insensitive-chars-p nats (list #\- #\=))
           (asgop-asg-sub))
          ((abnf::nats-match-insensitive-chars-p nats (list #\* #\=))
           (asgop-asg-mul))
          ((abnf::nats-match-insensitive-chars-p nats (list #\/ #\=))
           (asgop-asg-div))
          ((abnf::nats-match-insensitive-chars-p nats (list #\% #\=))
           (asgop-asg-rem))
          ((abnf::nats-match-insensitive-chars-p nats (list #\* #\* #\=))
           (asgop-asg-pow))
          ;; shift
          ((abnf::nats-match-insensitive-chars-p nats (list #\< #\< #\=))
           (asgop-asg-shl))
          ((abnf::nats-match-insensitive-chars-p nats (list #\> #\> #\=))
           (asgop-asg-shr))
          ;; bitwise
          ((abnf::nats-match-insensitive-chars-p nats (list #\& #\=))
           (asgop-asg-bitand))
          ((abnf::nats-match-insensitive-chars-p nats (list #\| #\=))
           (asgop-asg-bitior))
          ((abnf::nats-match-insensitive-chars-p nats (list #\^ #\=))
           (asgop-asg-bitxor))
          ;; boolean
          ((abnf::nats-match-insensitive-chars-p nats (list #\& #\& #\=))
           (asgop-asg-and))
          ((abnf::nats-match-insensitive-chars-p nats (list #\| #\| #\=))
           (asgop-asg-or))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-assignment-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract an @('assignment-statement') to a statement."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "assignment-statement"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf left) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf op) (abs-assignment-operator tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf right) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (make-statement-assign :op op :left left :right right))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-assert-call ((tree abnf::treep))
  :returns (cons console-resultp)
  :short "Abstract an @('assert-call') to a console function call."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "assert-call"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "assert"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree "("))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf expr) (abs-expression tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-ichars tree ")")))
    (console-assert expr))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod chars+exprs
  :short "Fixtype of pairs consisting of
          a list of Leo characters and a list of expressions."
  ((chars char-list)
   (exprs expression-list))
  :tag :chars+exprs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult chars+exprs-result
  :short "Fixtype of errors and lists of pairs consisting of
          a list of Leo characters and a list of expressions."
  :ok chars+exprs
  :pred chars+exprs-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-print-arguments ((tree abnf::treep))
  :returns (chars+exprs chars+exprs-resultp)
  :short "Abstract a @('print-arguments') to print arguments."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "print-arguments"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree "("))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf lit) (abs-string-literal tree))
       ((okf chars) (check-literal-is-string-literal lit))
       ((okf exprs) (abs-*-comma-expression sub.3rd))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (check-?-comma tree))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-ichars tree ")")))
    (make-chars+exprs :chars chars :exprs exprs))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-print-call ((tree abnf::treep))
  :returns (cons console-resultp)
  :short "Abstract a @('print-call') to a console function call."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "print-call"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf (chars+exprs chars+exprs)) (abs-print-arguments tree))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf tree) (abnf::check-tree-nonleaf-1-1 tree "print-function"))
       ((okf nats) (abnf::check-tree-leafterm tree)))
    (cond ((abnf::nats-match-sensitive-chars-p nats (str::explode "error"))
           (console-error chars+exprs.chars chars+exprs.exprs))
          ((abnf::nats-match-sensitive-chars-p nats (str::explode "log"))
           (console-log chars+exprs.chars chars+exprs.exprs))
          (t (reserrf (list :found-console-function nats)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-console-call ((tree abnf::treep))
  :returns (cons console-resultp)
  :short "Abstract a @('console-call') to a console function call."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "console-call"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "assert-call") (abs-assert-call tree))
          ((equal rulename? "print-call") (abs-print-call tree))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-console-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract a @('console-statement') to a console statement."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "console-statement"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "console"))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-ichars tree "."))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf ccall) (abs-console-call tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (statement-console ccall))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-finalize-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract a @('finalize-statement') to a Leo finalize statement."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "finalize-statement"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "async"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "finalize"))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf arguments) (abs-function-arguments tree))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-ichars tree ";")))

    (make-statement-finalize :arguments arguments))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-increment-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract an @('increment-statement') to a Leo increment statement."
  (b* (((okf (abnf::tree-list-tuple10 sub))
        (abnf::check-tree-nonleaf-10 tree "increment-statement"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "increment"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "("))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf mapping) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-schars tree ","))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf index) (abs-expression tree))

       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf &) (abnf::check-tree-schars tree ","))

       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf amount) (abs-expression tree))

       ((okf tree) (abnf::check-tree-list-1 sub.8th))
       ((okf ?) (check-?-comma tree))

       ((okf tree) (abnf::check-tree-list-1 sub.9th))
       ((okf &) (abnf::check-tree-schars tree ")"))

       ((okf tree) (abnf::check-tree-list-1 sub.10th))
       ((okf &) (abnf::check-tree-schars tree ";")))

    (make-statement-increment :mapping mapping
                              :index index
                              :amount amount))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-decrement-statement ((tree abnf::treep))
  :returns (stat statement-resultp)
  :short "Abstract an @('decrement-statement') to a Leo decrement statement."
  (b* (((okf (abnf::tree-list-tuple10 sub))
        (abnf::check-tree-nonleaf-10 tree "decrement-statement"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "decrement"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "("))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf mapping) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-schars tree ","))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf index) (abs-expression tree))

       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf &) (abnf::check-tree-schars tree ","))

       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf amount) (abs-expression tree))

       ((okf tree) (abnf::check-tree-list-1 sub.8th))
       ((okf ?) (check-?-comma tree))

       ((okf tree) (abnf::check-tree-list-1 sub.9th))
       ((okf &) (abnf::check-tree-schars tree ")"))

       ((okf tree) (abnf::check-tree-list-1 sub.10th))
       ((okf &) (abnf::check-tree-schars tree ";")))

    (make-statement-decrement :mapping mapping
                              :index index
                              :amount amount))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines abs-statements

  (define abs-statement ((tree abnf::treep))
    :returns (stat statement-resultp)
    :short "Abstract a @('statement') to a statement."
    (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "statement"))
         ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
      (cond ((equal rulename? "return-statement")
             (abs-return-statement tree))
            ((equal rulename? "variable-declaration")
             (b* (((okf var) (abs-variable-declaration tree)))
               (statement-let var)))
            ((equal rulename? "constant-declaration")
             (b* (((okf const) (abs-constant-declaration tree)))
               (statement-const const)))
            ((equal rulename? "conditional-statement")
             (abs-conditional-statement tree))
            ((equal rulename? "loop-statement")
             (abs-loop-statement tree))
            ((equal rulename? "assignment-statement")
             (abs-assignment-statement tree))
            ((equal rulename? "console-statement")
             (abs-console-statement tree))
            ((equal rulename? "finalize-statement")
             (abs-finalize-statement tree))
            ((equal rulename? "increment-statement")
             (abs-increment-statement tree))
            ((equal rulename? "decrement-statement")
             (abs-decrement-statement tree))
            ((equal rulename? "block")
             (b* (((okf stats) (abs-block tree)))
               (statement-block stats)))
            (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  (define abs-*-statement ((trees abnf::tree-listp))
    :returns (stats statement-list-resultp)
    :short "Abstract a @('*statement') to a list of statements."
    (b* (((when (endp trees)) nil)
         ((okf stat) (abs-statement (car trees)))
         ((okf stats) (abs-*-statement (cdr trees))))
      (cons stat stats))
    :measure (abnf::tree-list-count trees))

  (define abs-block ((tree abnf::treep))
    :returns (stats statement-list-resultp)
    :short "Abstract a @('block') to a list of statements."
    (b* (((okf (abnf::tree-list-tuple3 sub)) (abnf::check-tree-nonleaf-3 tree "block"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-ichars tree "{"))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf &) (abnf::check-tree-ichars tree "}")))
      (abs-*-statement sub.2nd))
    :measure (abnf::tree-count tree))

  (define abs-branch ((tree abnf::treep))
    :returns (branch branch-resultp)
    :short "Abstract a @('branch') to a branch."
    (b* (((okf (abnf::tree-list-tuple3 sub))
          (abnf::check-tree-nonleaf-3 tree "branch"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-schars tree "if"))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf expr) (abs-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf stats) (abs-block tree)))
      (make-branch :test expr :body stats))
    :measure (abnf::tree-count tree))

  (define abs-conditional-statement ((tree abnf::treep))
    :returns (stat statement-resultp)
    :short "Abstract a @('conditional-statement') to a statement."
    (b* (((okf treess) (abnf::check-tree-nonleaf tree "conditional-statement")))
      (case (len treess)
        (1 (b* (((okf trees) (abnf::check-tree-list-list-1 treess))
                ((okf tree) (abnf::check-tree-list-1 trees))
                ((okf branch) (abs-branch tree)))
             (make-statement-if :branches (list branch)
                                :else nil)))
        (3 (b* (((okf (abnf::tree-list-tuple3 sub))
                 (abnf::check-tree-list-list-3 treess))
                ((okf tree) (abnf::check-tree-list-1 sub.1st))
                ((okf branch) (abs-branch tree))
                ((okf tree) (abnf::check-tree-list-1 sub.2nd))
                ((okf &) (abnf::check-tree-schars tree "else"))
                ((okf tree) (abnf::check-tree-list-1 sub.3rd))
                ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
             (cond ((equal rulename? "block")
                    (b* (((okf stats) (abs-block tree)))
                      (make-statement-if :branches (list branch)
                                         :else stats)))
                   ((equal rulename? "conditional-statement")
                    (b* (((okf stat) (abs-conditional-statement tree))
                         ((unless (statement-case stat :if))
                          (reserrf (list :not-if-statement stat)))
                         ((statement-if stat) stat))
                      (make-statement-if :branches (cons branch
                                                         stat.branches)
                                         :else stat.else)))
                   (t (reserrf
                       (list :found-subtree (abnf::tree-info-for-error tree)))))))
        (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
    :measure (abnf::tree-count tree))

  (define abs-loop-statement ((tree abnf::treep))
    :returns (stat statement-resultp)
    :short "Abstract a @('loop-statement') to a statement."
    (b* (((okf (abnf::tree-list-tuple10 sub))
          (abnf::check-tree-nonleaf-10 tree "loop-statement"))
         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-schars tree "for"))
         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf id) (abs-identifier tree))
         ((okf tree) (abnf::check-tree-list-1 sub.3rd))
         ((okf &) (abnf::check-tree-ichars tree ":"))
         ((okf tree) (abnf::check-tree-list-1 sub.4th))
         ((okf type) (abs-type tree))
         ((okf tree) (abnf::check-tree-list-1 sub.5th))
         ((okf &) (abnf::check-tree-schars tree "in"))
         ((okf tree) (abnf::check-tree-list-1 sub.6th))
         ((okf from) (abs-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.7th))
         ((okf &) (abnf::check-tree-ichars tree ".."))
         ((okf tree) (abnf::check-tree-list-1 sub.8th))
         ((okf has-=?) (check-optional-equals-p tree))
         ((okf tree) (abnf::check-tree-list-1 sub.9th))
         ((okf to) (abs-expression tree))
         ((okf tree) (abnf::check-tree-list-1 sub.10th))
         ((okf block) (abs-block tree)))
      (make-statement-for :name id
                          :type type
                          :from from
                          :to to
                          :inclusivep has-=?
                          :body block))
    :measure (abnf::tree-count tree))

  :prepwork ((set-bogus-mutual-recursion-ok t))

  :returns-hints
  (("Goal"
    :in-theory
    (enable
     statementp-when-statement-resultp-and-not-reserrp
     statement-listp-when-statement-list-resultp-and-not-reserrp)))

  :verify-guards nil ; done below
  ///
  (verify-guards abs-statement)

  (fty::deffixequiv-mutual abs-statements))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-function-parameter ((tree abnf::treep))
  :returns (fpar funparam-resultp)
  :short "Abstract a @('function-parameter') to a function parameter."
  (b* (((okf (abnf::tree-list-tuple4 sub))
        (abnf::check-tree-nonleaf-4 tree "function-parameter"))
       ((okf sort)
        (b* (((okf tree) (abnf::check-tree-list-1 sub.1st))
             ((okf treess) (abnf::check-tree-nonleaf tree nil))
             ((when (endp treess)) (var/const-sort-private))
             ((okf trees) (abnf::check-tree-list-list-1 treess))
             ((okf tree) (abnf::check-tree-list-1 trees))
             (public? (abnf::check-tree-schars tree "public"))
             ((when (not (reserrp public?))) (var/const-sort-public))
             (constant? (abnf::check-tree-schars tree "constant"))
             ((when (not (reserrp constant?))) (var/const-sort-constant))
             (const? (abnf::check-tree-schars tree "const"))
             ((when (not (reserrp const?))) (var/const-sort-const)))
          (reserrf (list :found-subtree (abnf::tree-info-for-error tree)))))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf name) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ":"))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf type) (abs-type tree)))
    (make-funparam :name name :sort sort :type type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-comma-function-parameter ((tree abnf::treep))
  :returns (fpar funparam-resultp)
  :short "Abstract a @('( \",\" function-parameter )')
          to a function parameters."
  (b* (((okf (abnf::tree-list-tuple2 sub)) (abnf::check-tree-nonleaf-2 tree nil))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree ","))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-function-parameter tree))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-comma-function-parameter ((trees abnf::tree-listp))
  :returns (fpars
            funparam-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               funparamp-when-funparam-resultp-and-not-reserrp
               funparam-listp-when-funparam-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( \",\" function-parameter )')
          to a list of function parameters."
  (b* (((when (endp trees)) nil)
       ((okf fpar) (abs-comma-function-parameter (car trees)))
       ((okf fpars) (abs-*-comma-function-parameter (cdr trees))))
    (cons fpar fpars))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-function-parameters ((tree abnf::treep))
  :returns (fpars
            funparam-list-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               funparamp-when-funparam-resultp-and-not-reserrp
               funparam-listp-when-funparam-list-resultp-and-not-reserrp))))
  :short "Abstract a @('function-parameters') to a list of function parameters."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "function-parameters"))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf fpar) (abs-function-parameter tree))
       ((okf fpars) (abs-*-comma-function-parameter sub.2nd))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (check-?-comma tree)))
    (cons fpar fpars))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-?-function-parameters ((tree abnf::treep))
  :returns (params funparam-list-resultp)
  :short "Abstract a @('[ function-parameters ]')
          to list of function parameters."
  (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
       ((when (endp treess)) nil)
       ((okf trees) (abnf::check-tree-list-list-1 treess))
       ((okf tree) (abnf::check-tree-list-1 trees)))
    (abs-function-parameters tree))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-function-declaration ((tree abnf::treep))
  :returns (fundef fundecl-resultp)
  :short "Abstract a @('function-declaration') to a function declaration."
  (b* (((okf (abnf::tree-list-tuple9 sub))
        (abnf::check-tree-nonleaf-9 tree "function-declaration"))
       ((okf anns) (abs-*-annotation sub.1st))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "function"))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf name) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-schars tree "("))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf params) (abs-?-function-parameters tree))
       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf &) (abnf::check-tree-schars tree ")"))
       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf &) (abnf::check-tree-schars tree "->"))
       ((okf tree) (abnf::check-tree-list-1 sub.8th))
       ((okf type) (abs-type tree))
       ((okf tree) (abnf::check-tree-list-1 sub.9th))
       ((okf body) (abs-block tree)))
    (make-fundecl :annotations anns
                  :sort (fun-sort-standard)
                  :name name
                  :inputs params
                  :output type
                  :body body))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This should be in an ABNF utilities file.
(define empty-optional-tree-p ((tree abnf::treep))
  :returns (y/n booleanp)
  (and (abnf::tree-case tree :nonleaf)
       (equal (abnf::tree-nonleaf->rulename? tree) nil)
       (equal (abnf::tree-nonleaf->branches tree) nil))
  :hooks (:fix))

(define abs-?-output-type ((tree abnf::treep))
  :returns (final type-option-resultp)
  :short "Abstract an optional type (parsed from @('[ \"->\" type ]') to a @('type-option')."

  (if (empty-optional-tree-p tree)
      ;; in this case there was no finalizer block
      nil

    (b* (((okf (abnf::tree-list-tuple2 sub))
          (abnf::check-tree-nonleaf-2 tree ""))

         ((okf tree) (abnf::check-tree-list-1 sub.1st))
         ((okf &) (abnf::check-tree-schars tree "->"))

         ((okf tree) (abnf::check-tree-list-1 sub.2nd))
         ((okf type) (abs-type tree)))
      type))
  :hooks (:fix))

(define abs-finalizer ((tree abnf::treep))
  :returns (final finalizer-resultp)
  :short "Abstract a @('[ finalizer ]') to a Leo finalizer."

  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "finalizer"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "finalize"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-schars tree "("))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf params) (abs-?-function-parameters tree))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-schars tree ")"))

       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf type?) (abs-?-output-type tree))

       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf body) (abs-block tree)))

    (make-finalizer :name name
                    :inputs params
                    :output type?
                    :body body))
  :hooks (:fix))

(define abs-?-finalizer ((tree abnf::treep))
  :returns (final finalizer-option-resultp)
  :short "Abstract a @('[ finalizer ]') to a @('finalizer-option')."

  (if (empty-optional-tree-p tree)
      ;; in this case there was no finalizer block
      nil

    (b* (((okf treess) (abnf::check-tree-nonleaf tree nil))
         ((when (endp treess)) nil)
         ((okf trees) (abnf::check-tree-list-list-1 treess))
         ((okf tree) (abnf::check-tree-list-1 trees)))
      (abs-finalizer tree)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-transition-declaration ((tree abnf::treep))
  :returns (fundef fundecl-resultp)
  :short "Abstract a @('transition-declaration') to a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A transition is a function of sort @('fun-sort-transition')."))
  (b* (((okf (abnf::tree-list-tuple10 sub))
        (abnf::check-tree-nonleaf-10 tree "transition-declaration"))
       ((okf anns) (abs-*-annotation sub.1st))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree "transition"))
       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf name) (abs-identifier tree))
       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf &) (abnf::check-tree-schars tree "("))
       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf params) (abs-?-function-parameters tree))
       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf &) (abnf::check-tree-schars tree ")"))
       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf &) (abnf::check-tree-schars tree "->"))
       ((okf tree) (abnf::check-tree-list-1 sub.8th))
       ((okf type) (abs-type tree))
       ((okf tree) (abnf::check-tree-list-1 sub.9th))
       ((okf body) (abs-block tree))
       ((okf tree) (abnf::check-tree-list-1 sub.10th))
       ((okf finalizer?) (abs-?-finalizer tree)))

    (make-fundecl :annotations anns
                  :sort (fun-sort-transition)
                  :name name
                  :inputs params
                  :output type
                  :body body
                  :finalizer finalizer?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-struct-component-declaration ((tree abnf::treep))
  :returns (ret-comp compdecl-resultp)
  :short "Abstract a @('struct-component-declaration') to a @('compdecl')."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "struct-component-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf &) (abnf::check-tree-schars tree ":"))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf type) (abs-type tree)))
    (make-compdecl :name name
                   :type type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-comma-struct-component-declaration ((tree abnf::treep))
  :returns (ret-comp compdecl-resultp)
  :short "Abstract a @('( \",\" struct-component-declaration )') to a @('compdecl')."
  (b* (((okf (abnf::tree-list-tuple2 sub)) (abnf::check-tree-nonleaf-2 tree nil))
       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-ichars tree ","))
       ((okf tree) (abnf::check-tree-list-1 sub.2nd)))
    (abs-struct-component-declaration tree))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-comma-struct-component-declaration ((trees abnf::tree-listp))
  :returns
  (ret-comps
   compdecl-list-resultp
        :hints
        (("Goal"
          :in-theory
          (enable
           compdeclp-when-compdecl-resultp-and-not-reserrp
           compdecl-listp-when-compdecl-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*( \",\" struct-component-declaration )') to a list of @('compdecl')."
  (b* (((when (endp trees)) nil)
       ((okf comp) (abs-comma-struct-component-declaration (car trees)))
       ((okf comps) (abs-*-comma-struct-component-declaration (cdr trees))))
    (cons comp comps))
  :hooks (:fix)
  ///

  (defret compdecl-listp-of-abs-*-comma-struct-component-declaration
    (implies (not (reserrp ret-comps))
             (compdecl-listp ret-comps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-struct-component-declarations ((tree abnf::treep))
  :returns
  (ret-comps
   compdecl-list-resultp
        :hints
        (("Goal"
          :in-theory
          (enable
           compdeclp-when-compdecl-resultp-and-not-reserrp
           compdecl-listp-when-compdecl-list-resultp-and-not-reserrp))))
  :short "Abstract a @('struct-component-declarations') to a list of @('compdecl')."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "struct-component-declarations"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf comp) (abs-struct-component-declaration tree))

       ((okf comps) (abs-*-comma-struct-component-declaration sub.2nd))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (check-?-comma tree)))
    (cons comp comps))
  :hooks (:fix)
  ///

  (defret compdecl-listp-of-abs-struct-component-declarations
    (implies (not (reserrp ret-comps))
             (compdecl-listp ret-comps))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-struct-declaration ((tree abnf::treep))
  :returns (structdef structdecl-resultp)
  :short "Abstract a @('struct-declaration') to a struct declaration."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "struct-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "struct"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-schars tree "{"))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf compdecls) (abs-struct-component-declarations tree))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-schars tree "}")))
    (make-structdecl :name name
                     :components compdecls
                     :recordp nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-record-declaration ((tree abnf::treep))
  :returns (recdef structdecl-resultp)
  :short "Abstract a @('record-declaration') to a struct declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that a record declaration is just a special kind of struct declaration."))
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "record-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "record"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-schars tree "{"))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf compdecls) (abs-struct-component-declarations tree))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-schars tree "}")))
    (make-structdecl :name name
                     :components compdecls
                     :recordp t))
  :hooks (:fix))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-mapping-declaration ((tree abnf::treep))
  :returns (mappingdef mappingdecl-resultp)
  :short "Abstract a @('mapping-declaration') to a mapping declaration."
  (b* (((okf (abnf::tree-list-tuple7 sub))
        (abnf::check-tree-nonleaf-7 tree "mapping-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "mapping"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf name) (abs-identifier tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-schars tree ":"))

       ((okf tree) (abnf::check-tree-list-1 sub.4th))
       ((okf domtype) (abs-type tree))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-schars tree "=>"))

       ((okf tree) (abnf::check-tree-list-1 sub.6th))
       ((okf rngtype) (abs-type tree))

       ((okf tree) (abnf::check-tree-list-1 sub.7th))
       ((okf &) (abnf::check-tree-schars tree ";")))
    (make-mappingdecl :name name
                      :domain-type domtype
                      :range-type rngtype))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; remove later
(define abs-declaration ((tree abnf::treep))
  :returns (decl topdecl-resultp)
  :short "Abstract a @('declaration') to a top-level declaration."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "declaration"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "function-declaration")
           (b* (((okf fun) (abs-function-declaration tree)))
             (topdecl-function fun)))
          ((equal rulename? "transition-declaration")
           (b* (((okf fun) (abs-transition-declaration tree)))
             (topdecl-function fun)))
          ((equal rulename? "struct-declaration")
           (b* (((okf sdecl) (abs-struct-declaration tree)))
             (topdecl-struct sdecl)))
          ((equal rulename? "record-declaration")
           (b* (((okf rdecl) (abs-record-declaration tree)))
             (topdecl-struct rdecl))) ; a record is a kind of struct
          ((equal rulename? "mapping-declaration")
           (b* (((okf mdecl) (abs-mapping-declaration tree)))
             (topdecl-mapping mdecl)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; remove later
(define abs-*-declaration ((trees abnf::tree-listp))
  :returns
  (defs
    topdecl-list-resultp
    :hints
    (("Goal"
      :in-theory
      (enable
       topdeclp-when-topdecl-resultp-and-not-reserrp
       topdecl-listp-when-topdecl-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*declaration') to a list of top-level declarations."
  (b* (((when (endp trees)) nil)
       ((okf decl) (abs-declaration (car trees)))
       ((okf decls) (abs-*-declaration (cdr trees))))
    (cons decl decls))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-program-item ((tree abnf::treep))
  :returns (decl topdecl-resultp)
  :short "Abstract a @('program-item') to a @('topdecl')."
  (b* (((okf tree) (abnf::check-tree-nonleaf-1-1 tree "program-item"))
       ((okf rulename?) (abnf::check-tree-nonleaf? tree)))
    (cond ((equal rulename? "function-declaration")
           (b* (((okf fun) (abs-function-declaration tree)))
             (topdecl-function fun)))
          ((equal rulename? "transition-declaration")
           (b* (((okf fun) (abs-transition-declaration tree)))
             (topdecl-function fun)))
          ((equal rulename? "struct-declaration")
           (b* (((okf sdecl) (abs-struct-declaration tree)))
             (topdecl-struct sdecl)))
          ((equal rulename? "record-declaration")
           (b* (((okf rdecl) (abs-record-declaration tree)))
             (topdecl-struct rdecl))) ; a record is a kind of struct
          ((equal rulename? "mapping-declaration")
           (b* (((okf mdecl) (abs-mapping-declaration tree)))
             (topdecl-mapping mdecl)))
          (t (reserrf (list :found-subtree (abnf::tree-info-for-error tree))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-program-item ((trees abnf::tree-listp))
  :returns
  (defs
    topdecl-list-resultp
    :hints
    (("Goal"
      :in-theory
      (enable
       topdeclp-when-topdecl-resultp-and-not-reserrp
       topdecl-listp-when-topdecl-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*program-item') to a list of @('topdecl')."
  (b* (((when (endp trees)) nil)
       ((okf decl) (abs-program-item (car trees)))
       ((okf decls) (abs-*-program-item (cdr trees))))
    (cons decl decls))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-program-declaration ((tree abnf::treep))
  :returns (decl programdecl-resultp)
  :short "Abstract a @('program-declaration') to a @('programdecl')."
  (b* (((okf (abnf::tree-list-tuple5 sub))
        (abnf::check-tree-nonleaf-5 tree "program-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "program"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf id) (abs-program-id tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree "{"))

       ((okf items) (abs-*-program-item sub.4th))

       ((okf tree) (abnf::check-tree-list-1 sub.5th))
       ((okf &) (abnf::check-tree-ichars tree "}")))
    (make-programdecl :id id
                      :items items))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-import-declaration ((tree abnf::treep))
  :returns (decl importdecl-resultp)
  :short "Abstract a @('import-declaration') to an @('importdecl')."
  (b* (((okf (abnf::tree-list-tuple3 sub))
        (abnf::check-tree-nonleaf-3 tree "import-declaration"))

       ((okf tree) (abnf::check-tree-list-1 sub.1st))
       ((okf &) (abnf::check-tree-schars tree "import"))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf progid) (abs-program-id tree))

       ((okf tree) (abnf::check-tree-list-1 sub.3rd))
       ((okf &) (abnf::check-tree-ichars tree ";")))
    (make-importdecl :program progid))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-*-import-declaration ((trees abnf::tree-listp))
  :returns
  (defs
    importdecl-list-resultp
    :hints
    (("Goal"
      :in-theory
      (enable
       importdeclp-when-importdecl-resultp-and-not-reserrp
       importdecl-listp-when-importdecl-list-resultp-and-not-reserrp))))
  :short "Abstract a @('*declaration') to a list of import declarations."
  (b* (((when (endp trees)) nil)
       ((okf decl) (abs-import-declaration (car trees)))
       ((okf decls) (abs-*-import-declaration (cdr trees))))
    (cons decl decls))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define abs-file ((tree abnf::treep))
  :returns (file file-resultp)
  :short "Abstract a @('file') to a file."
  (b* (((okf (abnf::tree-list-tuple2 sub))
        (abnf::check-tree-nonleaf-2 tree "file"))

       ((okf imports) (abs-*-import-declaration sub.1st))

       ((okf tree) (abnf::check-tree-list-1 sub.2nd))
       ((okf program) (abs-program-declaration tree)))
    (make-file :imports imports
               :program program))
  :hooks (:fix))
