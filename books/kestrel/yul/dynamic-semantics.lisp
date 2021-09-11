; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte16-list" :dir :system)
(include-book "kestrel/fty/ubyte256" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-semantics
  :parents (yul)
  :short "Dynamic semantics of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the dynamic semantics of Yul
     by formalizing the Yul computation state
     and by defining functions that manipulate the computation state
     via execution of the Yul abstract syntax.")
   (xdoc::p
    "This is based on the formal specification in
     [Yul: Specification of Yul: Formal Specification],
     which defines an interpreter for Yul."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod value
  :short "Fixtype of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "Yul, being generic, is parameterized over
     a collection of supported types and their values.
     For the EVM dialect of Yul, which is our initial interest,
     the only supported type is @('u256'), i.e. unsigned 256-bit integers.
     So for now we define values as wrapped unsigned 256-bit integers.
     As explained in the "
    (xdoc::seetopic "static-semantics" "static semantics")
    ", for now we do not have explicit types,
     i.e. we have just one type.
     This matches the fact that we have just one kind of values.")
   (xdoc::p
    "We should extend and genearalize this."))
  ((get ubyte256))
  :tag :value
  :pred valuep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-list
  :short "Fixtype of lists of values."
  :elt-type value
  :true-listp t
  :elementp-of-nil nil
  :pred value-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult value-result
  :short "Fixtype of errors and values."
  :ok value
  :pred value-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap lstate
  :short "Fixtype of local states."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of local state object as
     a finite map from identifiers to values."))
  :key-type identifier
  :val-type value
  :pred lstatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cstate
  :short "Fixtype of computational states."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     this consists of a local state object and a global state object.
     The latter is generic in generic Yul.
     For now, for simplicity, we ignore the global state completely,
     and just defined a computational state as a (wrapped) local state.")
   (xdoc::p
    "We plan to extend this notion of computation states
     to also include the Yul global state."))
  ((local lstate))
  :tag :cstate
  :pred cstatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum mode
  :short "Fixtype of modes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[Yul: Specification of Yul: Formal Specification] introduces
     the notion of mode, which indicates how a statement completes execution."))
  (:regular ())
  (:break ())
  (:continue ())
  (:leave ())
  :pred modep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod eoutcome
  :short "Fixtype of expression outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     the execution of an expression results in
     not only zero of more values,
     but also possibly updated global and local states.
     [Yul: Specification of Yul: Formal Specification]
     does not have an explicit name for this notion,
     which in our formalization consists of
     a computation state and a list of values.
     We call this an expression outcome."))
  ((cstate cstate)
   (values value-list))
  :tag :eoutcome
  :pred eoutcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod soutcome
  :short "Fixtype of statement outcomes."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to [Yul: Specification of Yul: Formal Specification],
     the execution of a statement results in
     not only possibly updated global and local states,
     but also a mode.
     [Yul: Specification of Yul: Formal Specification]
     does not have an explicit name for this notion,
     which in our formalization consists of
     a computation state and a mode.
     We call this a statement outcome."))
  ((cstate cstate)
   (mode mode))
  :tag :soutcome
  :pred soutcomep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte16-to-utf8 ((codepoint acl2::ubyte16p))
  :returns (bytes acl2::ubyte8-listp
                  :hints (("Goal" :in-theory (enable acl2::ubyte8p
                                                     acl2::ubyte16p
                                                     acl2::ubyte16-fix))))
  :short "UTF-8 encoding of a 16-bit Unicode code point."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation of plain string literals in Yul
     involves turning Unicode escapes into their UTF-8 encodings.
     This function does that.")
   (xdoc::p
    "The encoding is as follows (e.g. see "
    (xdoc::ahref "https://en.wikipedia.org/wiki/UTF-8"
                 "the Wikipedia page on UTF-8")
    "):")
   (xdoc::ul
    (xdoc::li
     "A code point between 0 and 7Fh,
      which consists of 7 bits @('abcdefg'),
      is encoded as one byte @('0abcdefg').")
    (xdoc::li
     "A code point between 80h and 7FFh,
      which consists of 8 to 11 bits @('abcdefghijk'),
      is encoded as two bytes @('110abcde 10fghijk').")
    (xdoc::li
     "A code point between 800h and FFFFh,
      which consists of 12 to 16 bits @('abcdefghijklmnop'),
      is encoded as three bytes @('1110abcd 10efghij 10klmnop').")))
  (b* ((codepoint (acl2::ubyte16-fix codepoint)))
    (cond ((<= codepoint #x7f) (list codepoint))
          ((<= codepoint #x7ff) (list (logior #b11000000
                                              (ash codepoint -6))
                                      (logior #b10000000
                                              (logand codepoint
                                                      #b111111))))
          ((<= codepoint #xffff) (list (logior #b11100000
                                               (ash codepoint -12))
                                       (logior #b10000000
                                               (logand (ash codepoint -6)
                                                       #b111111))
                                       (logior #b10000000
                                               (logand codepoint
                                                       #b111111))))
          (t (acl2::impossible))))
  :guard-hints (("Goal" :in-theory (enable acl2::ubyte16p)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))
             (local (include-book "ihs/logops-lemmas" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-pair ((hp hex-pairp))
  :returns (val acl2::ubyte8p
                :hints (("Goal"
                         :in-theory (enable acl2::ubyte8p
                                            str::hex-digit-chars-value))))
  :short "Evaluate a pair of hex digits to an 8-bit unsigned integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The digits are interpreted in big endian form."))
  (str::hex-digit-chars-value
   (list (hex-digit->get (hex-pair->1st hp))
         (hex-digit->get (hex-pair->2nd hp))))
  :prepwork ((local (include-book "arithmetic/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-quad ((hq hex-quadp))
  :returns (val acl2::ubyte16p
                :hints (("Goal"
                         :in-theory (enable acl2::ubyte16p
                                            str::hex-digit-chars-value))))
  :short "Evaluate a quadruple of hex digits to a 16-bit unsigned integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The digits are interpreted in big endian form."))
  (str::hex-digit-chars-value
   (list (hex-digit->get (hex-quad->1st hq))
         (hex-digit->get (hex-quad->2nd hq))
         (hex-digit->get (hex-quad->3rd hq))
         (hex-digit->get (hex-quad->4th hq))))
  :prepwork ((local (include-book "arithmetic/top" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-escape ((esc escapep))
  :returns (bytes acl2::ubyte8-listp)
  :short "Evaluate an escape to a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation of plain string literals involves
     first turning the string into a sequence of bytes.
     Here we turn an escape into a sequence of bytes.
     An escape consisting of a backslash followed by a single character
     is turned into a singleton byte list with the character's code.
     A @('\x...') escape is turned into a singleton byte list
     with the value of the escape.
     A @('\u...') escape is turned into a list of 1, 2, or 3 bytes
     that is the UTF-8 encoding of the code point."))
  (escape-case esc
               :single-quote (list (char-code #\'))
               :double-quote (list (char-code #\"))
               :letter-n (list 10)
               :letter-r (list 13)
               :letter-t (list 9)
               :line-feed (list 10)
               :carriage-return (list 13)
               :x (list (eval-hex-pair esc.get))
               :u (ubyte16-to-utf8 (eval-hex-quad esc.get)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-string-element ((elem string-elementp))
  :returns (bytes acl2::ubyte8-listp
                  :hints (("Goal" :in-theory (enable acl2::ubyte8p))))
  :short "Evaluate a string element to a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation of plain string literals involves
     first turning the string into a sequence of bytes.
     An escape is turned into a list of bytes
     as formalized in @(tsee eval-escape).
     A single character is turned into a singleton list
     consisting of the character's code."))
  (string-element-case
   elem
   :char (list (char-code elem.get))
   :escape (eval-escape elem.get))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-string-element-list ((elems string-element-listp))
  :returns (bytes acl2::ubyte8-listp)
  :short "Evaluate a list of string elements to a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We concatenate the lists of bytes for the elements."))
  (cond ((endp elems) nil)
        (t (append (eval-string-element (car elems))
                   (eval-string-element-list (cdr elems)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-plain-string-literal ((content string-element-listp))
  :returns (val value-resultp)
  :short "Evaluate a plain string literal to a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A plain string literal consists of
     a list of string elements
     and a flag indicating whether the surrounding quotes are double or single
     (see @(tsee literal)).
     The flag does not affect the value of the literal,
     so this function only takes the list of string elements as arguments.")
   (xdoc::p
    "We convert the list of string elements to a list of bytes.
     If the resulting bytes exceed 32 in number, it is an error.
     Otherwise, we pad the list with 0 bytes on the right to reach 32 bytes,
     and we turn the resulting list of 32 bytes to a 256-bit unsigned integer.
     This evaluation is not described in detail in [Yul],
     but it was explained via discussions on Gitter,
     and [Yul] is being extended with these explanations."))
  (b* ((bytes (eval-string-element-list content))
       ((unless (<= (len bytes) 32))
        (err (list :plain-string-too-long bytes)))
       (bytes (append bytes (repeat (- 32 (len bytes)) 0))))
    (value (acl2::bebytes=>nat bytes)))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::ubyte256p
                       acl2::bebytes=>nat)
    :use (:instance acl2::bendian=>nat-upper-bound
          (base 256)
          (digits (append
                   (eval-string-element-list content)
                   (repeat (- 32 (len (eval-string-element-list content)))
                           0))))))
  :hooks (:fix)

  :prepwork

  ((defrulel lemma1
     (implies (acl2::ubyte8p x)
              (acl2::bytep x))
     :enable acl2::bytep)

   (defrulel lemma2
     (implies (acl2::ubyte8-listp x)
              (acl2::byte-listp x))
     :enable (acl2::byte-listp acl2::ubyte8-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-pair-list ((hps hex-pair-listp))
  :returns (bytes acl2::ubyte8-listp)
  :short "Evaluate a list of hex pairs to a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done element-wise:
     each pair is turned into a byte,
     and the order is preserved."))
  (cond ((endp hps) nil)
        (t (cons (eval-hex-pair (car hps))
                 (eval-hex-pair-list (cdr hps)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-string-literal ((content hex-pair-listp))
  :returns (val value-resultp)
  :short "Evaluate a hex string literal to a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "A hex string literal consists of
     a list of hex pairs
     and a flag indicating whether the surrounding quotes are double or single
     (see @(tsee literal)).
     The flag does not affect the value of the literal,
     so this function only takes the list of hex pairs as arguments.")
   (xdoc::p
    "We convert the list of hex pairs to a list of bytes.
     If the resulting bytes exceed 32 in number, it is an error.
     Otherwise, we pad the list with 0 bytes on the right to reach 32 bytes,
     and we turn the resulting list of 32 bytes to a 256-bit unsigned integer.
     This evaluation is not described in detail in [Yul],
     but it was explained via discussions on Gitter,
     and [Yul] is being extended with these explanations."))
  (b* ((bytes (eval-hex-pair-list content))
       ((unless (<= (len bytes) 32))
        (err (list :hex-string-too-long bytes)))
       (bytes (append bytes (repeat (- 32 (len bytes)) 0))))
    (value (acl2::bebytes=>nat bytes)))
  :guard-hints
  (("Goal"
    :in-theory (enable acl2::ubyte256p
                       acl2::bebytes=>nat)
    :use (:instance acl2::bendian=>nat-upper-bound
          (base 256)
          (digits (append
                   (eval-hex-pair-list content)
                   (repeat (- 32 (len (eval-hex-pair-list content)))
                           0))))))
  :hooks (:fix)

  :prepwork

  ((defrulel lemma1
     (implies (acl2::ubyte8p x)
              (acl2::bytep x))
     :enable acl2::bytep)

   (defrulel lemma2
     (implies (acl2::ubyte8-listp x)
              (acl2::byte-listp x))
     :enable (acl2::byte-listp acl2::ubyte8-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-literal ((lit literalp))
  :returns (val value-resultp)
  :short "Evaluate a literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since for now our only values are 256-bit unsigned integers,
     we evaluate boolean literals to 0 (for false) and 1 (for true).
     This is not described in [Yul], but it was discussed on Gitter.
     This should apply to at least the EVM dialect of Yul,
     while other dialects that include a boolean type
     may need to evaluate boolean literals differently.
     We will generalize this aspect of our formalization at some point.")
   (xdoc::p
    "A decimal or hexadecimal literal evaluates to the number it represents.
     This number must fit in 256 bits, otherwise it is an error.")
   (xdoc::p
    "Plain and hex strings are evaluated as described in
     @(tsee eval-plain-string-literal) and @(tsee eval-hex-string-literal)."))
  (literal-case
   lit
   :boolean (if lit.get (value 1) (value 0))
   :dec-number (if (acl2::ubyte256p lit.get)
                   (value lit.get)
                 (err (list :dec-number-too-large lit.get)))
   :hex-number (b* ((num (str::hex-digit-chars-value
                          (hex-digit-list->chars lit.get))))
                 (if (acl2::ubyte256p num)
                     (value num)
                   (err (list :hex-number-too-large lit.get))))
   :plain-string (eval-plain-string-literal lit.content)
   :hex-string (eval-hex-string-literal lit.content))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: continue
