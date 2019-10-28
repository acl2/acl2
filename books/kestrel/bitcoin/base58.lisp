; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "kestrel/utilities/lists/index-of-theorems" :dir :system)
(include-book "std/util/defval" :dir :system)

(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ base58
  :parents (bitcoin)
  :short "Base58 encoding and decoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Base58 encoding is described in
     <a href=\"https://en.bitcoin.it/wiki/Base58Check_encoding\"
     >Page `Base58Check encoding' of [Wiki]</a>;
     Base58 encoding is part of Base58Check encoding.
     Base58 encoding is also described
     in Section `Base58 and Base58Check Encoding' of Chapter 4 of [MB].
     [WP] does not mention Base58 encoding.")
   (xdoc::p
    "Base58 decoding is the inverse of Base58 encoding."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *base58-characters*
  :short "List of characters used in Base58 encoding."
  :long
  (xdoc::topstring
   (xdoc::p
    "These characters are listed in the table in "
    (xdoc::a
     :href "https://en.bitcoin.it/wiki/Base58Check_encoding#Base58_symbol_chart"
      "Section `Base58 symbol chart' of Page `Base58Check encoding' of [Wiki]")
    ", along with their corresponding values in base 58.
     This list is ordered according to increasing values."))
  (explode "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz")
  ///

  (assert-event (character-listp *base58-characters*))

  (assert-event (equal (len *base58-characters*) 58))

  (assert-event (no-duplicatesp *base58-characters*)))

(defval *base58-zero*
  :short "Character that encodes 0 in the Base58 encoding."
  :long
  (xdoc::topstring-p
   "This is the first character of @(tsee *base58-characters*).")
  (car *base58-characters*)
  ///

  (assert-event (equal *base58-zero* #\1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58-characterp (x)
  :returns (yes/no booleanp)
  :parents (base58-character)
  :short "Recognizer for @(tsee base58-character)."
  (if (member x *base58-characters*) t nil)
  ///

  (defrule characterp-when-base58-characterp
    (implies (base58-characterp x)
             (characterp x))
    :rule-classes :compound-recognizer))

(std::deffixer base58-character-fix
  :pred base58-characterp
  :body-fix *base58-zero*
  :parents (base58-character)
  :short "Fixer for @(tsee base58-character).")

(defsection base58-character-fix-ext
  :extension base58-character-fix
  (defret characterp-of-base58-character-fix
    (characterp fixed-x)
    :rule-classes :type-prescription))

(defsection base58-character
  :short "Base58 characters."
  :long
  (xdoc::topstring-p
   "These are the characters in @(tsee *base58-characters*).")
  (fty::deffixtype base58-character
    :pred base58-characterp
    :fix base58-character-fix
    :equiv base58-character-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist base58-character-list
  :short "True lists of Base58 characters."
  :elt-type base58-character
  :true-listp t
  :elementp-of-nil nil
  :pred base58-character-listp
  ///

  (defrule character-listp-when-base58-character-listp
    (implies (base58-character-listp x)
             (character-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58-valuep (x)
  :returns (yes/no booleanp)
  :parents (base58-value)
  :short "Recognizer for @(tsee base58-value)."
  (dab-digitp 58 x)
  ///

  (defrule natp-when-base58-valuep
    (implies (base58-valuep x)
             (natp x))
    :rule-classes :compound-recognizer)

  (defrule below-58-when-base58-valuep
    (implies (base58-valuep x)
             (< x 58))
    :rule-classes :forward-chaining
    :enable dab-digitp)

  (defruled base58-valuep-rewrite-dab-digitp-58
    (equal (base58-valuep x)
           (dab-digitp 58 x)))

  (defruled dab-digitp-58-rewrite-base58-valuep
    (equal (dab-digitp 58 x)
           (base58-valuep x)))

  (theory-invariant (incompatible
                     (:rewrite base58-valuep-rewrite-dab-digitp-58)
                     (:rewite dab-digitp-58-rewrite-base58-valuep))))

(define base58-value-fix ((x base58-valuep))
  :returns (fixed-x base58-valuep)
  :parents (base58-value)
  :short "Fixer for @(tsee base58-value)."
  (dab-digit-fix 58 x)
  :prepwork ((local (in-theory (enable base58-valuep))))
  ///

  (more-returns
   (fixed-x natp :rule-classes :type-prescription)
   (fixed-x (< fixed-x 58)
            :name base58-value-fix-upper-bound
            :rule-classes :linear))

  (defrule base58-value-fix-when-base58-valuep
    (implies (base58-valuep x)
             (equal (base58-value-fix x) x))))

(defsection base58-value
  :short "Base58 values."
  :long
  (xdoc::topstring-p
   "These are digits in base 58.")
  (fty::deffixtype base58-value
    :pred base58-valuep
    :fix base58-value-fix
    :equiv base58-value-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist base58-value-list
  :short "True lists of Base58 values."
  :elt-type base58-value
  :true-listp t
  :elementp-of-nil nil
  :pred base58-value-listp
  ///

  (defrule nat-listp-when-base58-value-listp
    (implies (base58-value-listp x)
             (nat-listp x))
    :enable base58-value-listp)

  (defruled base58-value-listp-rewrite-dab-digit-listp-58
    (equal (base58-value-listp x)
           (dab-digit-listp 58 x))
    :enable (base58-value-listp
             dab-digit-listp
             base58-valuep-rewrite-dab-digitp-58))

  (defruled dab-digit-listp-58-rewrite-base58-value-listp
    (equal (dab-digit-listp 58 x)
           (base58-value-listp x))
    :enable (base58-value-listp
             dab-digit-listp
             dab-digitp-58-rewrite-base58-valuep))

  (theory-invariant (incompatible
                     (:rewrite base58-value-listp-rewrite-dab-digit-listp-58)
                     (:rewrite dab-digit-listp-58-rewrite-base58-value-listp)))

  (defruled base58-value-list-fix-rewrite-dab-digit-list-fix-58
    (equal (base58-value-list-fix x)
           (dab-digit-list-fix 58 x))
    :enable (base58-value-list-fix dab-digit-list-fix base58-value-fix))

  (defruled dab-digit-list-fix-58-rewrite-base58-value-list-fix
    (equal (dab-digit-list-fix 58 x)
           (base58-value-list-fix x))
    :enable (base58-value-list-fix dab-digit-list-fix base58-value-fix))

  (theory-invariant (incompatible
                     (:rewrite
                      base58-value-list-fix-rewrite-dab-digit-list-fix-58)
                     (:rewrite
                      dab-digit-list-fix-58-rewrite-base58-value-list-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58-val=>char ((val base58-valuep))
  :returns (char base58-characterp
                 :hints (("Goal" :in-theory (enable base58-value-fix))))
  :short "Turn a Base58 value into the corresponding character."
  :long
  (xdoc::topstring-p
   "The correspondence is given
    in the table
    in Section `Base58 symbol chart'
    of Page `Base58Check encoding'
    of [Wiki].
    Since the list @(tsee *base58-characters*)
    is ordered according to increasing values,
    this function is essentially @(tsee nth).")
  (nth (base58-value-fix val) *base58-characters*)
  :guard-hints (("Goal" :in-theory (enable base58-valuep)))
  :hooks (:fix))

(define base58-char=>val ((char base58-characterp))
  :returns (val base58-valuep
                :hints (("Goal" :in-theory (enable base58-character-fix
                                                   base58-characterp))))
  :short "Turn a Base58 character into the corresponding value."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee base58-val=>char).")
  (index-of (base58-character-fix char) *base58-characters*)
  :hooks (:fix))

(defsection base58-val<=>char-inverses-theorems
  :parents (base58-val=>char base58-char=>val)
  :short "@(tsee base58-val=>char) and @(tsee base58-char=>val)
          are mutual inverses."

  (defrule base58-char=>val=>char
    (equal (base58-val=>char (base58-char=>val char))
           (base58-character-fix char))
    :enable (base58-char=>val base58-character-fix base58-characterp))

  (defrule base58-val=>char=>val
    (equal (base58-char=>val (base58-val=>char val))
           (base58-value-fix val))
    :enable (base58-char=>val base58-val=>char)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58-vals=>chars ((vals base58-value-listp))
  :returns (chars base58-character-listp)
  :short "Lift @(tsee base58-val=>char) to lists."
  (cond ((endp vals) nil)
        (t (cons (base58-val=>char (car vals))
                 (base58-vals=>chars (cdr vals)))))
  :hooks (:fix)
  ///

  (defrule len-of-base58-vals=>chars
    (equal (len (base58-vals=>chars vals))
           (len vals)))

  (defrule base58-vals=>chars-of-append
    (equal (base58-vals=>chars (append vals1 vals2))
           (append (base58-vals=>chars vals1)
                   (base58-vals=>chars vals2)))
    :enable base58-vals=>chars)

  (defrule base58-vals=>chars-of-repeat
    (equal (base58-vals=>chars (repeat n val))
           (repeat n (base58-val=>char val)))
    :enable (base58-vals=>chars repeat)))

(define base58-chars=>vals ((chars base58-character-listp))
  :returns (vals base58-value-listp)
  :short "Lift @(tsee base58-char=>val) to lists."
  (cond ((endp chars) nil)
        (t (cons (base58-char=>val (car chars))
                 (base58-chars=>vals (cdr chars)))))
  :hooks (:fix)
  ///

  (defrule len-of-base58-chars=>vals
    (equal (len (base58-chars=>vals chars))
           (len chars)))

  (defrule base58-chars=>vals-of-append
    (equal (base58-chars=>vals (append chars1 chars2))
           (append (base58-chars=>vals chars1)
                   (base58-chars=>vals chars2)))
    :enable base58-chars=>vals)

  (defrule base58-chars=>vals-of-repeat
    (equal (base58-chars=>vals (repeat n char))
           (repeat n (base58-char=>val char)))
    :enable (base58-chars=>vals repeat)))

(defsection base58-vals<=>chars-inverses-theorems
  :parents (base58-vals=>chars base58-chars=>vals)
  :short "@(tsee base58-vals=>chars) and @(tsee base58-chars=>vals)
          are mutual inverses."

  (defrule base58-chars=>vals=>chars
    (equal (base58-vals=>chars (base58-chars=>vals chars))
           (base58-character-list-fix chars))
    :enable (base58-chars=>vals base58-vals=>chars))

  (defrule base58-vals=>chars=>vals
    (equal (base58-chars=>vals (base58-vals=>chars vals))
           (base58-value-list-fix vals))
    :enable (base58-chars=>vals base58-vals=>chars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define base58-encode ((bytes byte-listp))
  :returns (chars base58-character-listp)
  :short "Turn a list of bytes into
          the corresponding list of Base58 characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described in bullets 4, 5, and 6 in
     <a href=\"https://en.bitcoin.it/wiki/Base58Check_encoding#Creating_a_Base58Check_string\"
     >Section `Creating a Base58Check string' of Page `Base58Check encoding'
     of [Wiki]</a>.")
   (xdoc::p
    "The bytes are treated as big bendian digits in base 256
     and converted into the natural number that they denote.
     This natural number is converted into
     a minimal-length list of big endian digits in base 58,
     which has no leading zeros.
     These digits are converted into the corresponding characters.
     The number of zeros in the input bytes is
     the difference between the number of all those bytes
     and the result of removing all their leading zero bytes.
     As many @('1') characters (which correspond to value 0 in base 58)
     as this number of zero bytes are added before the other character.
     The resulting characters are returned as a string.")
   (xdoc::p
    "The addition of the ``zero'' (i.e. @('1')) characters
     does not affect the denoted natural number,
     which is the same denoted by the input bytes.")
   (xdoc::p
    "Note that @(tsee trim-bendian*) fixes its argument
     to a true list of natural numbers, not to a true list of bytes.
     Thus, we use an @(tsee mbe) there,
     so that the encoding function fixes its input to a true list of bytes."))
  (b* ((nat (bebytes=>nat bytes))
       (vals (nat=>bendian* 58 nat))
       (number-of-zeros (- (len bytes)
                           (len (trim-bendian*
                                 (mbe :logic (byte-list-fix bytes)
                                      :exec bytes)))))
       (chars (append (repeat number-of-zeros *base58-zero*)
                      (base58-vals=>chars vals))))
    chars)
  :guard-hints (("Goal"
                 :in-theory
                 (enable base58-value-listp-rewrite-dab-digit-listp-58)))
  :hooks (:fix)
  ///

  (defruled base58-encode-same-natural-number
    (equal (bendian=>nat 58 (base58-chars=>vals (base58-encode bytes)))
           (bebytes=>nat bytes))
    :enable (acl2::bendian=>nat-of-append
             base58-value-listp-rewrite-dab-digit-listp-58)))

(define base58-decode ((chars base58-character-listp))
  :returns (bytes byte-listp)
  :short "Turn a list of Base58 characters
          into the corresponding list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not explicitly described in [Wiki] or [MB],
     but is, implicitly, the inverse of encoding.")
   (xdoc::p
    "From a formal specification perspective,
     we could define this function as the inverse of @(tsee base58-encode).
     But since decoding is quite analogous to encoding,
     and not more complicated than encoding,
     instead we define it in an executable way,
     and prove that it is indeed the inverse of encoding.
     This way, the formal specification of decoding is executable.")
   (xdoc::p
    "This executable formal specification of decoding essentially runs
     the encoding steps ``in reverse''.
     Instead of counting
     the number of leading ``zero'' (i.e. @('1')) characters
     in the input characters,
     we count the number of leading zeros in their corresponding values,
     via @(tsee trim-bendian*).
     Unlike in @(tsee base58-encode),
     there is no need here for an @(tsee mbe)
     to fix the argument of @(tsee trim-bendian*).")
   (xdoc::p
    "The addition of the zero bytes does not affect the denoted natural number,
     which is the same denoted by
     (the corresponding values of) the input characters."))
  (b* ((vals (base58-chars=>vals chars))
       (nat (bendian=>nat 58 vals))
       (number-of-zeros (- (len vals)
                           (len (trim-bendian* vals))))
       (bytes (append (repeat number-of-zeros 0)
                      (nat=>bebytes* nat))))
    bytes)
  :hooks (:fix)
  :guard-hints (("Goal"
                 :in-theory
                 (enable dab-digit-listp-58-rewrite-base58-value-listp)))
  ///

  (defruled base58-decode-same-natural-number
    (equal (bebytes=>nat (base58-decode chars))
           (bendian=>nat 58 (base58-chars=>vals chars)))
    :enable acl2::bebytes=>nat-of-append))

(defsection base58-encode/decode-inverses-theorems
  :parents (base58-encode base58-decode)
  :short "@(tsee base58-encode) and @(tsee base58-decode)
          are mutual inverses."

  (defrule base58-decode-of-base58-encode
    (equal (base58-decode (base58-encode bytes))
           (byte-list-fix bytes))
    :enable (base58-encode
             base58-decode
             base58-value-list-fix-rewrite-dab-digit-list-fix-58
             acl2::bendian=>nat-of-append)
    :use (:instance acl2::append-of-repeat-and-trim-bendian*
          (acl2::digits (byte-list-fix bytes)))
    :disable acl2::append-of-repeat-and-trim-bendian*
    :prep-books ((include-book "arithmetic/top" :dir :system)))

  (defrule base58-encode-of-base58-decode
    (equal (base58-encode (base58-decode chars))
           (base58-character-list-fix chars))
    :enable (base58-encode
             base58-decode
             acl2::bebytes=>nat-of-append
             dab-digit-list-fix-58-rewrite-base58-value-list-fix)
    :use ((:instance acl2::append-of-repeat-and-trim-bendian*
           (acl2::digits (base58-chars=>vals chars)))
          (:instance lemma
           (x (append (repeat (+ (len chars)
                                 (- (len (trim-bendian*
                                          (base58-chars=>vals chars)))))
                              0)
                      (trim-bendian* (base58-chars=>vals chars))))
           (y (base58-chars=>vals chars))))
    :disable acl2::append-of-repeat-and-trim-bendian*
    :prep-books ((include-book "arithmetic/top" :dir :system))
    :prep-lemmas
    ((defrule lemma
       (implies (equal x y)
                (equal (base58-vals=>chars x)
                       (base58-vals=>chars y)))
       :rule-classes nil))))
