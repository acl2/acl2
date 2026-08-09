; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HASH")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "kestrel/bv-lists/byte-listp-def" :dir :system)

(include-book "kestrel/data/utilities/bit-vectors/bitops-defs" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))

(local (include-book "kestrel/data/utilities/bit-vectors/bitops" :dir :system))

(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))

(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We don't seem to have good rules about logtail
(local (in-theory (disable acl2::right-shift-to-logtail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ serialization
  :parents (hashes)
  :short "A serialization of arbitrary ACL2 objects into byte lists."
  :long
  (xdoc::topstring
    (xdoc::p
      "Our hash functions are factored into two components: a serialization of
       the object into a list of bytes, and a hash algorithm over that byte
       list. This book provides the first component, @(tsee to-bytes), which is
       shared by every hash function we define.")
    (xdoc::p
      "The map is designed to be injective, except that all bad atoms share one
       encoding. See @(tsee to-bytes-injective). Consequently, hash collisions
       arise only from the compression performed by the hash algorithm
       itself.")
    (xdoc::ul
      (xdoc::li
        "Each object is prefixed with a byte identifying its type (cons,
         symbol, string, character, integer, rational, complex, or
         bad-atom).")
      (xdoc::li
        "Natural numbers are serialized in unsigned LEB128 form: little-endian
         groups of 7 bits (base-128 digits), where the high bit of each byte
         indicates whether another byte follows. This form is self-delimiting.
         Integers are first mapped to naturals by interleaving the nonnegative
         and negative integers (0, -1, 1, -2, 2, ... map to 0, 1, 2, 3, 4,
         ...), the so-called ``zigzag'' encoding.")
      (xdoc::li
        "Strings are length-prefixed (the length in LEB128 form) followed by
         their character codes.")
      (xdoc::li
        "Compound atoms serialize their parts in sequence: symbols as their
         package name and symbol name (each length-prefixed), rationals as
         numerator and denominator (self-delimiting LEB128 encodings), and
         numbers as their real and imaginary parts."))
    (xdoc::p
      "These functions are specifications. They are executable, but no attempt
       is made to execute them efficiently; a hash function is expected to fuse
       the serialization into its own walk over the object, and to appeal to
       these definitions only in its logical story.")
    (xdoc::p
      "In particular, a fused pass can produce the LEB128 form of a large
       integer by recursively splitting the integer roughly in half (at a
       multiple of 7 bits), so that the work is @($O(k\\log(k))$) in the bit
       length @($k$), rather than the @($O(k^2)$) which would result from
       extracting one group at a time. The split lemmas justifying this
       computation are proved in this book.")
    (xdoc::p
      "Finally, we note that the length of the produced byte list corresponds
       with the size of the object, <i>without</i> optimization for
       shared substructure."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The type tag bytes used by the serialization. Every atom (and cons)
;; contributes exactly one of these bytes before its contents, so that objects
;; of different types never share a byte list.
;;
;; The particular values are arbitrary; injectivity requires only that they
;; be distinct (checked below), and the hash algorithms are insensitive to
;; the choice. Note that changing them changes every hash value.

(defconst *tag-cons* #x70)
(defconst *tag-symbol* #x71)
(defconst *tag-string* #x72)
(defconst *tag-character* #x73)
(defconst *tag-integer* #x74)
(defconst *tag-rational* #x75)
(defconst *tag-complex* #x76)
(defconst *tag-bad-atom* #x77)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *type-tags*
  (list *tag-cons*
        *tag-symbol*
        *tag-string*
        *tag-character*
        *tag-integer*
        *tag-rational*
        *tag-complex*
        *tag-bad-atom*))

;; Sanity check
(rule
  (no-duplicatesp *type-tags*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel <-of-loghead-7-and-128-linear
  (< (loghead 7 x) 128)
  :rule-classes :linear
  :use (:instance acl2::unsigned-byte-p-of-loghead
                  (acl2::size1 7)
                  (acl2::size 7)
                  (acl2::i x))
  :disable acl2::unsigned-byte-p-of-loghead)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-to-bytes ((n natp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a natural number in unsigned LEB128 form."
  :long
  (xdoc::topstring
    (xdoc::p
      "The number is split into 7-bit groups &mdash; its base-128 digits
       &mdash; and each byte carries one group, least significant first. The
       high bit is set on every byte but the last, so the encoding is
       self-delimiting. No redundant zero high-order group (the base-128
       analogue of a leading zero) is ever emitted, so the encoding is
       canonical.")
    (xdoc::p
      "This is the unsigned "
      (xdoc::a :href "https://en.wikipedia.org/wiki/LEB128" "LEB128")
      " encoding (as in DWARF and WebAssembly), also known as the base-128
       ``varint'' encoding of Protocol Buffers. VLQ is the analogous
       big-endian (most significant group first) encoding."))
  :returns (bytes byte-listp)
  (let ((n (lnfix n)))
    (if (< n 128)
        (list n)
      (cons (+ 128 (loghead 7 n))
            (nat-to-bytes (ash n -7)))))
  :measure (nfix n))

;;;;;;;;;;;;;;;;;;;;

(defrule nat-to-bytes-type-prescription
  (and (consp (nat-to-bytes n))
       (true-listp (nat-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (nat-to-bytes n)))
  :induct t
  :enable nat-to-bytes)

(defrule nat-to-bytes-when-nat-equiv-congruence
  (implies (nat-equiv n0 n1)
           (equal (nat-to-bytes n0)
                  (nat-to-bytes n1)))
  :rule-classes :congruence
  :expand ((nat-to-bytes n0)
           (nat-to-bytes n1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nat-to-leb128-groups ((n natp) (m natp))
  (declare (xargs :type-prescription :none))
  :short "Serialize exactly @('m') 7-bit groups (base-128 digits) of a
          natural number, each with the continuation bit set."
  :long
  (xdoc::topstring
    (xdoc::p
      "This describes the low portion of the LEB128 serialization of a large
       number, whose continuation bits are all set because more significant
       groups always follow. It is the specification for hash implementations
       which serialize a large number by splitting it into portions, rather
       than extracting one group at a time (see @(tsee nat-to-bytes-split)
       and, e.g., @(see jenkins-one-at-a-time))."))
  :returns (bytes byte-listp)
  (if (zp m)
      nil
    (cons (+ 128 (loghead 7 n))
          (nat-to-leb128-groups (ash (lnfix n) -7) (1- m))))
  :measure (nfix m))

;;;;;;;;;;;;;;;;;;;;

(defrule nat-to-leb128-groups-type-prescription
  (true-listp (nat-to-leb128-groups n m))
  :rule-classes ((:type-prescription :typed-term (nat-to-leb128-groups n m)))
  :induct t
  :enable nat-to-leb128-groups)

(defrule nat-to-leb128-groups-when-nat-equiv-congruence
  (implies (nat-equiv m0 m1)
           (equal (nat-to-leb128-groups n m0)
                  (nat-to-leb128-groups n m1)))
  :rule-classes :congruence
  :expand ((nat-to-leb128-groups n m0)
           (nat-to-leb128-groups n m1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splitting a number at a multiple of 7 bits commutes with serialization:
;; the low bits contribute their groups (with continuation bits set), and the
;; high bits contribute the rest. These two rules justify serializing a large
;; number by divide and conquer.

(defruledl <-of-128-becomes-integer-length
  (implies (natp n)
           (equal (< n 128)
                  (< (integer-length n) 8)))
  :cases ((equal n 0)))

;; This rule inverts acl2::<-of-integer-length-arg1/arg2; enabling it together
;; with either loops.
(local (theory-invariant
         (incompatible! (:rewrite <-of-128-becomes-integer-length)
                        (:rewrite acl2::<-of-integer-length-arg1))))
(local (theory-invariant
         (incompatible! (:rewrite <-of-128-becomes-integer-length)
                        (:rewrite acl2::<-of-integer-length-arg2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (define groups-split-induct (n m m1)
    (if (zp m1)
        (list n m)
      (groups-split-induct (logtail 7 n) (1- m) (1- m1)))
    :measure (nfix m1)
    :verify-guards nil))

(local (in-theory (enable (:i groups-split-induct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nat-to-leb128-groups-split
  ;; The (natp n) hypothesis cannot be dropped: for negative n the first group
  ;; takes loghead of n's two's-complement bits while the recursion nfixes n
  ;; to 0 (e.g. n = -5, m = 2, m1 = 1 falsifies the unconditional statement).
  (implies (and (natp n)
                (natp m)
                (natp m1)
                (<= m1 m))
           (equal (nat-to-leb128-groups n m)
                  (append
                    (nat-to-leb128-groups (loghead (* 7 m1) n) m1)
                    (nat-to-leb128-groups (logtail (* 7 m1) n)
                                          (- m m1)))))
  :induct (groups-split-induct n m m1)
  :enable (nat-to-leb128-groups
           acl2::right-shift-to-logtail))

(defruled nat-to-bytes-split
  (implies (and (natp n)
                (natp m1)
                (< (* 7 m1) (integer-length n)))
           (equal (nat-to-bytes n)
                  (append
                    (nat-to-leb128-groups (loghead (* 7 m1) n) m1)
                    (nat-to-bytes (logtail (* 7 m1) n)))))
  :induct (groups-split-induct n nil m1)
  :expand ((nat-to-bytes n))
  :enable (nat-to-leb128-groups
           <-of-128-becomes-integer-length
           acl2::right-shift-to-logtail)
  :disable (acl2::<-of-integer-length-arg1
            acl2::<-of-integer-length-arg2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-contents-to-bytes ((n integerp))
  (declare (xargs :type-prescription :none))
  :short "Serialize an integer in LEB128 form, without a type tag."
  :long
  (xdoc::topstring
    (xdoc::p
      "The integer is first mapped to a natural number by the ``zigzag''
       encoding, which interleaves the nonnegative and negative integers.")
    (xdoc::p
      "Zigzag is preferred over a sign prefix because this function is also
       used in tagless positions (e.g. the numerator of a rational), where a
       sign would cost a full byte; folded into the LEB128 encoding it costs
       one bit.
       This is also the encoding of the signed varints of Protocol
       Buffers."))
  :returns (bytes byte-listp)
  (nat-to-bytes (if (< n 0)
                    (+ -1 (* -2 n))
                  (* 2 n))))

;;;;;;;;;;;;;;;;;;;;

(defrule integer-contents-to-bytes-type-prescription
  (and (consp (integer-contents-to-bytes n))
       (true-listp (integer-contents-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (integer-contents-to-bytes n)))
  :enable integer-contents-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-to-bytes ((n integerp))
  (declare (xargs :type-prescription :none))
  :short "Serialize an integer."
  :returns (bytes byte-listp)
  (cons *tag-integer* (integer-contents-to-bytes n)))

;;;;;;;;;;;;;;;;;;;;

(defrule integer-to-bytes-type-prescription
  (and (consp (integer-to-bytes n))
       (true-listp (integer-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (integer-to-bytes n)))
  :enable integer-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rational-contents-to-bytes ((n rationalp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a rational number, without a type tag."
  :long
  (xdoc::topstring
    (xdoc::p
      "The numerator (as a zigzag LEB128 encoding) followed by the denominator
       (in LEB128 form). Both parts are self-delimiting, so the pair is
       unambiguous."))
  :returns (bytes byte-listp)
  (append (integer-contents-to-bytes (numerator n))
          (nat-to-bytes (denominator n))))

;;;;;;;;;;;;;;;;;;;;

(defrule rational-contents-to-bytes-type-prescription
  (and (consp (rational-contents-to-bytes n))
       (true-listp (rational-contents-to-bytes n)))
  :rule-classes
  ((:type-prescription :typed-term (rational-contents-to-bytes n)))
  :enable rational-contents-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rational-to-bytes ((n rationalp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a rational number."
  :returns (bytes byte-listp)
  (cons *tag-rational* (rational-contents-to-bytes n)))

;;;;;;;;;;;;;;;;;;;;

(defrule rational-to-bytes-type-prescription
  (and (consp (rational-to-bytes n))
       (true-listp (rational-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (rational-to-bytes n)))
  :enable rational-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define complex-rational-to-bytes ((n complex-rationalp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a complex rational number."
  :returns (bytes byte-listp)
  (cons *tag-complex*
        (append (rational-contents-to-bytes (realpart n))
                (rational-contents-to-bytes (imagpart n)))))

;;;;;;;;;;;;;;;;;;;;

(defrule complex-rational-to-bytes-type-prescription
  (and (consp (complex-rational-to-bytes n))
       (true-listp (complex-rational-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (complex-rational-to-bytes n)))
  :enable complex-rational-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define acl2-number-to-bytes ((n acl2-numberp))
  (declare (xargs :type-prescription :none))
  :short "Serialize an ACL2 number."
  :returns (bytes byte-listp)
  (cond ((integerp n)
         (integer-to-bytes n))
        ((rationalp n)
         (rational-to-bytes n))
        (t (complex-rational-to-bytes n))))

;;;;;;;;;;;;;;;;;;;;

(defrule acl2-number-to-bytes-type-prescription
  (and (consp (acl2-number-to-bytes n))
       (true-listp (acl2-number-to-bytes n)))
  :rule-classes ((:type-prescription :typed-term (acl2-number-to-bytes n)))
  :enable acl2-number-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define character-contents-to-bytes ((c characterp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a character, without a type tag."
  :long
  (xdoc::topstring
    (xdoc::p
      "The character code alone. Used for the characters of a string, which are
       delimited by the string's length prefix."))
  :returns (bytes byte-listp
                  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                                     integer-range-p))))
  (list (char-code c)))

;;;;;;;;;;;;;;;;;;;;

(defrule character-contents-to-bytes-type-prescription
  (and (consp (character-contents-to-bytes c))
       (true-listp (character-contents-to-bytes c)))
  :rule-classes
  ((:type-prescription :typed-term (character-contents-to-bytes c)))
  :enable character-contents-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define character-to-bytes ((c characterp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a character."
  :returns (bytes byte-listp)
  (cons *tag-character* (character-contents-to-bytes c)))

;;;;;;;;;;;;;;;;;;;;

(defrule character-to-bytes-type-prescription
  (and (consp (character-to-bytes c))
       (true-listp (character-to-bytes c)))
  :rule-classes ((:type-prescription :typed-term (character-to-bytes c)))
  :enable character-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define characters-to-bytes ((chars character-listp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a list of characters as their character codes."
  :returns (bytes byte-listp
                  :hints (("Goal" :induct t
                                  :in-theory (enable unsigned-byte-p
                                                     integer-range-p))))
  (if (atom chars)
      nil
    (cons (char-code (car chars))
          (characters-to-bytes (cdr chars)))))

;;;;;;;;;;;;;;;;;;;;

(defrule characters-to-bytes-type-prescription
  (true-listp (characters-to-bytes chars))
  :rule-classes ((:type-prescription :typed-term (characters-to-bytes chars)))
  :induct t
  :enable characters-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-contents-to-bytes ((str stringp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a string, without a type tag."
  :long
  (xdoc::topstring
    (xdoc::p
      "The string's length (in LEB128 form) followed by its character codes.
       Used
       for the package and name strings of a symbol."))
  :returns (bytes byte-listp)
  (append (nat-to-bytes (length str))
          (characters-to-bytes (coerce str 'list))))

;;;;;;;;;;;;;;;;;;;;

(defrule string-contents-to-bytes-type-prescription
  (and (consp (string-contents-to-bytes str))
       (true-listp (string-contents-to-bytes str)))
  :rule-classes
  ((:type-prescription :typed-term (string-contents-to-bytes str)))
  :enable string-contents-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string-to-bytes ((str stringp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a string."
  :returns (bytes byte-listp)
  (cons *tag-string* (string-contents-to-bytes str)))

;;;;;;;;;;;;;;;;;;;;

(defrule string-to-bytes-type-prescription
  (and (consp (string-to-bytes str))
       (true-listp (string-to-bytes str)))
  :rule-classes ((:type-prescription :typed-term (string-to-bytes str)))
  :enable string-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define symbol-to-bytes ((symbol symbolp))
  (declare (xargs :type-prescription :none))
  :short "Serialize a symbol."
  :long
  (xdoc::topstring
    (xdoc::p
      "The package name followed by the symbol name, each length-prefixed. By
       @('acl2::symbol-equality'), these two strings determine the symbol."))
  :returns (bytes byte-listp)
  (cons *tag-symbol*
        (append (string-contents-to-bytes (symbol-package-name symbol))
                (string-contents-to-bytes (symbol-name symbol)))))

;;;;;;;;;;;;;;;;;;;;

(defrule symbol-to-bytes-type-prescription
  (and (consp (symbol-to-bytes symbol))
       (true-listp (symbol-to-bytes symbol)))
  :rule-classes ((:type-prescription :typed-term (symbol-to-bytes symbol)))
  :enable symbol-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atom-to-bytes (x)
  (declare (xargs :type-prescription :none))
  :short "Serialize an atom."
  :guard (not (consp x))
  :returns (bytes byte-listp)
  (cond ((symbolp x)
         (symbol-to-bytes x))
        ((acl2-numberp x)
         (acl2-number-to-bytes x))
        ((stringp x)
         (string-to-bytes x))
        ((characterp x)
         (character-to-bytes x))
        (t ;; bad-atom
         (list *tag-bad-atom*))))

;;;;;;;;;;;;;;;;;;;;

(defrule atom-to-bytes-type-prescription
  (and (consp (atom-to-bytes x))
       (true-listp (atom-to-bytes x)))
  :rule-classes ((:type-prescription :typed-term (atom-to-bytes x)))
  :enable atom-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-bytes (x)
  :short "Serialize an arbitrary ACL2 object as a list of bytes."
  :long
  (xdoc::topstring
    (xdoc::p
      "A @('cons') contributes its tag byte followed by the serializations of
       its car and its cdr, in that order. An atom is serialized by @(tsee
       atom-to-bytes).")
    (xdoc::p
      "This map is injective on objects free of bad atoms. See @(tsee
       to-bytes-injective)."))
  :returns (bytes byte-listp
                  :hints (("Goal" :induct t)))
  (if (consp x)
      (cons *tag-cons*
            (append (to-bytes (car x))
                    (to-bytes (cdr x))))
    (atom-to-bytes x)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t to-bytes)))

(defrule to-bytes-type-prescription
  (and (consp (to-bytes x))
       (true-listp (to-bytes x)))
  :rule-classes ((:type-prescription :typed-term (to-bytes x)))
  :induct t
  :enable to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Eventually, this should be moved to a more neutral location.
;; It does not need to be part of this book.

(define no-bad-atoms-p (x)
  (declare (xargs :type-prescription :none))
  :short "Recognize objects built entirely from good atoms."
  :long
  (xdoc::topstring
    (xdoc::p
      "All bad atoms share a single encoding, so @(tsee to-bytes) is injective
       only on objects satisfying this predicate. Note that a bad atom may
       occur arbitrarily deep within a cons tree, so this cannot be a flat
       condition on @('x') alone."))
  :returns (yes/no booleanp)
  (if (consp x)
      (and (no-bad-atoms-p (car x))
           (no-bad-atoms-p (cdr x)))
    (not (bad-atom x))))

;;;;;;;;;;;;;;;;;;;;

(defrule no-bad-atoms-p-type-prescription
  (booleanp (no-bad-atoms-p x))
  :rule-classes ((:type-prescription :typed-term (no-bad-atoms-p x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injectivity.
;;
;; The serialization is not merely injective, it is prefix-free: no encoding is
;; a proper prefix of another. That stronger property is what makes the
;; induction go through, since the encoding of a cons concatenates the
;; encodings of its car and cdr with no delimiter between them. Accordingly,
;; each layer is proved in the form
;;
;;   (equal (append (ENCODE a) r1) (append (ENCODE b) r2))
;;     <-> (and (equal a b) (equal r1 r2))
;;
;; and injectivity falls out by taking both remainders to be nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Natural numbers. Rather than reason about two LEB128 encodings at once,
;; we define a
;; decoder and show that it recovers the number and leaves the remainder of the
;; byte list untouched. This needs only an induction on the number.

(defrulel +-of-loghead-7-and-*-of-128-and-ash
  (implies (natp n)
           (equal (+ (loghead 7 n) (* 128 (ash n -7)))
                  n))
  :enable (acl2::right-shift-to-logtail
           loghead
           logtail))

(local
  (define parse-leb128 (bytes)
    :returns (mv (n natp :rule-classes :type-prescription)
                 rest)
    (if (atom bytes)
        (mv 0 nil)
      (let ((b (nfix (car bytes))))
        (if (< b 128)
            (mv b (cdr bytes))
          (mv-let (hi rest)
                  (parse-leb128 (cdr bytes))
            (mv (+ (- b 128) (* 128 hi)) rest)))))
    :verify-guards nil))

(local
  (defrule parse-leb128-of-append-of-nat-to-bytes
    (equal (parse-leb128 (append (nat-to-bytes n) rest))
           (mv (nfix n) rest))
    :induct (nat-to-bytes n)
    :enable (nat-to-bytes parse-leb128)))

(defruled append-of-nat-to-bytes-equal
  (implies (and (natp n)
                (natp m))
           (equal (equal (append (nat-to-bytes n) r1)
                         (append (nat-to-bytes m) r2))
                  (and (equal n m)
                       (equal r1 r2))))
  :use ((:instance parse-leb128-of-append-of-nat-to-bytes (rest r1))
        (:instance parse-leb128-of-append-of-nat-to-bytes (n m) (rest r2)))
  :disable parse-leb128-of-append-of-nat-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Characters. Character codes are fixed-width, so the encodings of two
;; character lists of equal length are comparable position by position. The
;; length is supplied by the caller's LEB128 length prefix.

(defrulel equal-of-char-codes
  (implies (and (characterp x)
                (characterp y))
           (equal (equal (char-code x) (char-code y))
                  (equal x y)))
  :use (:instance acl2::equal-char-code (acl2::x x) (acl2::y y)))

(defruled append-of-characters-to-bytes-equal
  (implies (and (character-listp c1)
                (character-listp c2)
                (equal (len c1) (len c2)))
           (equal (equal (append (characters-to-bytes c1) r1)
                         (append (characters-to-bytes c2) r2))
                  (and (equal c1 c2)
                       (equal r1 r2))))
  :induct (acl2::cdr-cdr-induct c1 c2)
  :enable characters-to-bytes)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Strings. The LEB128 length prefix is self-delimiting and pins down how
;; many character codes follow.

(defrulel equal-of-coerce-lists
  (implies (and (stringp s1)
                (stringp s2))
           (equal (equal (coerce s1 'list) (coerce s2 'list))
                  (equal s1 s2)))
  :use ((:instance acl2::coerce-inverse-2 (acl2::x s1))
        (:instance acl2::coerce-inverse-2 (acl2::x s2)))
  :disable acl2::coerce-inverse-2)

(defruled append-of-string-contents-to-bytes-equal
  (implies (and (stringp s1)
                (stringp s2))
           (equal (equal (append (string-contents-to-bytes s1) r1)
                         (append (string-contents-to-bytes s2) r2))
                  (and (equal s1 s2)
                       (equal r1 r2))))
  :enable (string-contents-to-bytes
           append-of-nat-to-bytes-equal
           append-of-characters-to-bytes-equal
           length))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Integers. The zigzag map is a bijection from the integers to the naturals:
;; nonnegative integers become even naturals and negative integers become odd
;; ones, so the two cases cannot collide.

(defrulel not-equal-of-odd-and-negative-even
  (implies (and (integerp a)
                (integerp b))
           (not (equal (+ 1 (* 2 a)) (* -2 b))))
  :use (:instance acl2::equal-of-*-and-*-cancel
                  (acl2::x 2)
                  (acl2::y (+ a b))
                  (acl2::z 0))
  :disable acl2::equal-of-*-and-*-cancel)

(defruled append-of-integer-contents-to-bytes-equal
  (implies (and (integerp n)
                (integerp m))
           (equal (equal (append (integer-contents-to-bytes n) r1)
                         (append (integer-contents-to-bytes m) r2))
                  (and (equal n m)
                       (equal r1 r2))))
  :enable (integer-contents-to-bytes
           append-of-nat-to-bytes-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rationals. Both the numerator and the denominator are self-delimiting, and
;; together they determine the rational.

(defrulel equal-of-denominators-when-equal-of-numerators
  (implies (and (rationalp x)
                (rationalp y)
                (equal (numerator x) (numerator y)))
           (equal (equal (denominator x) (denominator y))
                  (equal x y)))
  :use ((:instance acl2::rational-implies2 (acl2::x x))
        (:instance acl2::rational-implies2 (acl2::x y)))
  :disable acl2::rational-implies2)

(defruled append-of-rational-contents-to-bytes-equal
  (implies (and (rationalp n)
                (rationalp m))
           (equal (equal (append (rational-contents-to-bytes n) r1)
                         (append (rational-contents-to-bytes m) r2))
                  (and (equal n m)
                       (equal r1 r2))))
  :enable (rational-contents-to-bytes
           append-of-integer-contents-to-bytes-equal
           append-of-nat-to-bytes-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Atoms. Two atoms of different types differ in their first byte, and within
;; each type the contents determine the atom. Symbols are determined by their
;; package name and symbol name (@('acl2::symbol-equality')), and complex
;; rationals by their real and imaginary parts.

(defrulel equal-of-symbol-names-when-equal-of-symbol-package-names
  (implies (and (symbolp s1)
                (symbolp s2)
                (equal (symbol-package-name s1) (symbol-package-name s2)))
           (equal (equal (symbol-name s1) (symbol-name s2))
                  (equal s1 s2)))
  :use (:instance acl2::symbol-equality
                  (acl2::s1 s1)
                  (acl2::s2 s2)))

(defrulel equal-of-imagparts-when-equal-of-realparts
  (implies (and (acl2-numberp x)
                (acl2-numberp y)
                (equal (realpart x) (realpart y)))
           (equal (equal (imagpart x) (imagpart y))
                  (equal x y)))
  :use ((:instance acl2::realpart-imagpart-elim (acl2::x x))
        (:instance acl2::realpart-imagpart-elim (acl2::x y)))
  :disable acl2::realpart-imagpart-elim)

(defruled append-of-atom-to-bytes-equal
  (implies (and (not (consp x))
                (not (consp y))
                (not (bad-atom x))
                (not (bad-atom y)))
           (equal (equal (append (atom-to-bytes x) r1)
                         (append (atom-to-bytes y) r2))
                  (and (equal x y)
                       (equal r1 r2))))
  :enable (atom-to-bytes
           symbol-to-bytes
           acl2-number-to-bytes
           integer-to-bytes
           rational-to-bytes
           complex-rational-to-bytes
           string-to-bytes
           character-to-bytes
           character-contents-to-bytes
           append-of-string-contents-to-bytes-equal
           append-of-integer-contents-to-bytes-equal
           append-of-rational-contents-to-bytes-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Arbitrary objects. The cons tag distinguishes a cons from every atom, and
;; the induction pairs the two objects while threading the remainders, so that
;; the car case may consume the cdr's bytes as its own remainder.

(defrulel not-equal-of-append-of-atom-to-bytes-and-cons-of-tag-cons
  (implies (not (consp x))
           (and (not (equal (append (atom-to-bytes x) r)
                            (cons *tag-cons* b)))
                (not (equal (cons *tag-cons* b)
                            (append (atom-to-bytes x) r)))))
  :enable (atom-to-bytes
           symbol-to-bytes
           acl2-number-to-bytes
           integer-to-bytes
           rational-to-bytes
           complex-rational-to-bytes
           string-to-bytes
           character-to-bytes))

(local (defun to-bytes-induct (x y r1 r2)
         (declare (xargs :measure (acl2-count x)))
         (if (and (consp x) (consp y))
             (list (to-bytes-induct (car x)
                                    (car y)
                                    (append (to-bytes (cdr x)) r1)
                                    (append (to-bytes (cdr y)) r2))
                   (to-bytes-induct (cdr x) (cdr y) r1 r2))
           (list x y r1 r2))))

(defruled append-of-to-bytes-equal
  (implies (and (no-bad-atoms-p x)
                (no-bad-atoms-p y))
           (equal (equal (append (to-bytes x) r1)
                         (append (to-bytes y) r2))
                  (and (equal x y)
                       (equal r1 r2))))
  :induct (to-bytes-induct x y r1 r2)
  :expand ((to-bytes x) (to-bytes y))
  :enable (no-bad-atoms-p
           append-of-atom-to-bytes-equal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule to-bytes-injective
  :parents (serialization to-bytes)
  :short "@(tsee to-bytes) is injective on objects free of bad atoms."
  (implies (and (no-bad-atoms-p x)
                (no-bad-atoms-p y))
           (equal (equal (to-bytes x) (to-bytes y))
                  (equal x y)))
  :use (:instance append-of-to-bytes-equal (r1 nil) (r2 nil)))
