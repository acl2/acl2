; Bitcoin -- Bitcoin Improvement Proposal (BIP) 39
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/crypto/pbkdf2-hmac-sha-512-placeholder" :dir :system)
(include-book "kestrel/crypto/sha-256-placeholder" :dir :system)
(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)
(include-book "kestrel/utilities/bits-and-ubyte11s-as-digits" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/util/defenum" :dir :system)

(include-book "bip39-english-words")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bip39
  :parents (bitcoin)
  :short "Bitcion Improvement Proposal (BIP) 39."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is described at "
    (xdoc::a
     :href "https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki"
      "this page in the @('bitcoin/bips') repository on GitHub")
    ", linked from "
    (xdoc::a :href "https://en.bitcoin.it/wiki/BIP_0039"
      "Page `BIP 0039' of [Wiki]")
    ". We refer to the document at the first URL as `[BIP39]'
     in the documentation below.")
   (xdoc::p
    (xdoc::a
     :href
      "https://github.com/ethereumbook/ethereumbook/blob/develop/05wallets.asciidoc"
      "Chapter 5 of the ``Mastering Ethereum'' book")
    " has some informative illustrations of BIP 39."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum bip39-entropy-size-p
  (128 160 192 224 256)
  :short "Possible sizes of the entropy in bits."
  :long
  "<p>
   These are the possible values of @('ENT') in the table in [BIP39].
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bip39-entropy
  :short "Entropy values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The entropy is a sequence of bits whose size is one of the allowed ones
     (see @(tsee bip39-entropy-size-p)).")
   (xdoc::p
    "We introduce a fixtype for the possible values of the entropy."))

  (define bip39-entropyp (x)
    :returns (yes/no booleanp)
    :parents (bip39-entropy)
    :short "Recognizer for @(tsee bip39-entropy)."
    (and (bit-listp x)
         (bip39-entropy-size-p (len x))
         t)
    :no-function t)

  (define bip39-entropy-fix ((x bip39-entropyp))
    :returns (fixed-x bip39-entropyp)
    :parents (bip39-entropy)
    :short "Fixer for @(tsee bip39-entropy)."
    (mbe :logic (if (bip39-entropyp x) x (repeat 128 0))
         :exec x)
    :no-function t
    ///
    (defrule bip39-entropy-fix-when-bip39-entropyp
      (implies (bip39-entropyp x)
               (equal (bip39-entropy-fix x)
                      x))))

  (fty::deffixtype bip39-entropy
    :pred bip39-entropyp
    :fix bip39-entropy-fix
    :equiv bip39-entropy-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-entropy-to-word-indexes ((entropy bip39-entropyp))
  :returns (indexes ubyte11-listp)
  :short "Turn an entropy value into a list of word indexes."
  :long
  (xdoc::topstring
   (xdoc::p
    "First, we create a checksum of the entropy
     by taking the first @('CS') bits of the SHA-256 hash of the entropy.
     Then we append the checksum after the entropy.
     The resulting sequence of bits is divided into 11-bit chunks,
     which become the indexes of the words of the mnemonic.")
   (xdoc::p
    "The numer of word indexes (i.e. the length of the result)
     is the value @('MS') in the table in [BIP39].
     This is calculated from @('ENT'), via @('CS') and @('ENT+CS'),
     as shown in the table in [BIP39].
     The theorem below replicates these calculations.
     The theorem is disabled by default,
     because the right-hand side expression,
     despite not involving this function,
     is relatively complex.")
   (xdoc::p
    "We also prove a validation theorem
     (disabled by default for the same reason as the other one)
     showing all the possible values of @('MS')
     based on the possible values of @('ENT')."))
  (b* ((entropy (bip39-entropy-fix entropy))
       (entropy-bytes (bits=>bebytes entropy))
       (hash-bytes (sha-256 entropy-bytes))
       (hash (bebytes=>bits hash-bytes))
       (checksum (take (/ (len entropy) 32) hash))
       (all-bits (append entropy checksum)))
    (bits=>beubyte11s all-bits))
  :no-function t
  :guard-hints (("Goal" :in-theory (enable bip39-entropyp
                                           bip39-entropy-size-p)))
  :hooks (:fix)
  ///

  (defruled len-of-bip39-entropy-to-word-indexes
    (equal (len (bip39-entropy-to-word-indexes entropy))
           (b* ((ent (len (bip39-entropy-fix entropy)))
                (cs (/ ent 32))
                (ent+cs (+ ent cs))
                (ms (/ ent+cs 11)))
             ms))
    :enable (bip39-entropyp
             bip39-entropy-size-p
             bip39-entropy-fix)
    :disable acl2::take-redefinition
    :prep-books ((include-book "arithmetic/top-with-meta" :dir :system)))

  (defruled values-of-len-of-bip39-entropy-to-word-indexes
    (implies (bip39-entropyp entropy)
             (equal (len (bip39-entropy-to-word-indexes entropy))
                    (case (len entropy)
                      (128 12)
                      (160 15)
                      (192 18)
                      (224 21)
                      (256 24))))
    :enable (len-of-bip39-entropy-to-word-indexes
             bip39-entropyp
             bip39-entropy-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-word-indexes-to-words ((indexes ubyte11-listp))
  :returns (words string-listp
                  :hints (("Goal" :in-theory (enable ubyte11p ubyte11-fix))))
  :short "Map each 11-bit index to a word from the predefined wordlist,
          which consists of 2,048 words."
  (cond ((endp indexes) nil)
        (t (cons (nth (ubyte11-fix (car indexes))
                      *bip39-english-words*)
                 (bip39-word-indexes-to-words (cdr indexes)))))
  :no-function t
  :prepwork ((local (include-book "std/typed-lists/string-listp" :dir :system)))
  :hooks (:fix)
  ///

  (defrule len-of-bip39-word-indexes-to-words
    (equal (len (bip39-word-indexes-to-words indexes))
           (len indexes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-words-to-mnemonic ((words string-listp))
  :returns (mnemonic stringp)
  :short "Turn a list of mnemonic words into a single string,
           i.e. the mnemonic."
  (str::join (str::string-list-fix words) " ")
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-entropy-to-mnemonic ((entropy bip39-entropyp))
  :returns (mnemonic stringp)
  :short "Turn an entropy value into a mnemonic."
  :long
  (xdoc::topstring-p
   "This is the composition of the three functions that map
    entropy to word indexes, word indexes to words, and words to mnemonic.")
  (b* ((indexes (bip39-entropy-to-word-indexes entropy))
       (words (bip39-word-indexes-to-words indexes))
       (mnemonic (bip39-words-to-mnemonic words)))
    mnemonic)
  :no-function t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-mnemonic-to-seed ((mnemonic stringp) (passphrase stringp))
  :returns (seed byte-listp)
  :short "Turn a mnemonic string into a seed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The mnemonic is also called a key since it is input to
     a key-stretching function, namely PBKDF2 HMAC-SHA-512.
     The mnemonic is the first input of PBKDF2 HMAC-SHA-512.")
   (xdoc::p
    "The second input of PBKDF2 HMAC-SHA-512 is the salt, which is a string.
     It is composed of the string constant ``@('mnemonic')''
     concatenated with an optional user-supplied passphrase.")
   (xdoc::p
    "PBKDF2 stretches the mnemonic and salt
     using 2,048 rounds of hashing with HMAC-SHA-512,
     producing a 512-bit (i.e. 64-byte) value.
     This is the seed, suitable as a BIP 32 seed.")
   (xdoc::p
    "Note that this function does not require the mnemonic string to be
     a space-separated sequence of mnemonic words.
     It accepts any string as mnemonic, as well as any string as passphrase."))
  (b* ((password (string=>nats mnemonic))
       (salt (string=>nats (string-append "mnemonic"
                                                (str::str-fix passphrase))))
       (iterations 2048)
       (length 64))
    (crypto::pbkdf2-hmac-sha-512 password salt iterations length))
  :no-function t
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::byte-listp-rewrite-unsigned-byte-listp)))
  ///

  (fty::deffixequiv bip39-mnemonic-to-seed
    :hints (("Goal" :in-theory (enable string=>nats))))

  (defrule len-of-bip39-mnemonic-to-seed
    (equal (len (bip39-mnemonic-to-seed mnemonic passphrase))
           64)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bip39-entropy-to-seed ((entropy bip39-entropyp) (passphrase stringp))
  :returns (seed byte-listp)
  :short "Turn an entropy value into a seed."
  :long
  (xdoc::topstring
   (xdoc::p
    "This combines @(tsee bip39-entropy-to-mnemonic)
     and @(tsee bip39-mnemonic-to-seed)."))
  (bip39-mnemonic-to-seed (bip39-entropy-to-mnemonic entropy) passphrase)
  :no-function t
  :hooks (:fix)
  ///

  (defrule len-of-bip39-entropy-to-seed
    (equal (len (bip39-entropy-to-seed entropy passphrase))
           64)))
