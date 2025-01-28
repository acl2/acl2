; Yul Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "abstract-syntax")
(include-book "values")
(include-book "errors")

(include-book "kestrel/fty/ubyte8-list" :dir :system)
(include-book "kestrel/fty/ubyte16-list" :dir :system)
(include-book "kestrel/utilities/bytes-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ literal-evaluation
  :parents (static-semantics dynamic-semantics)
  :short "Evaluation of Yul literals."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ubyte16-to-utf8 ((codepoint ubyte16p))
  :returns (bytes ubyte8-listp
                  :hints (("Goal" :in-theory (enable ubyte8p
                                                     ubyte16p
                                                     ubyte16-fix))))
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
  (b* ((codepoint (ubyte16-fix codepoint)))
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
          (t (impossible))))
  :guard-hints (("Goal" :in-theory (enable ubyte16p)))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))
             (local (include-book "ihs/logops-lemmas" :dir :system)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-pair ((hp hex-pairp))
  :returns (val ubyte8p
                :hints (("Goal"
                         :in-theory (enable ubyte8p
                                            str::hex-digit-chars-value))))
  :short "Evaluate a pair of hex digits to a byte."
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
  :returns (val ubyte16p
                :hints (("Goal"
                         :in-theory (enable ubyte16p
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
  :returns (bytes ubyte8-listp)
  :short "Evaluate an escape to a list of bytes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation of plain string literals involves
     first turning the string into a sequence of bytes.
     Here we turn an escape into a sequence of bytes.
     An escape consisting of a backslash followed by a single character
     is turned into a singleton byte list with the character's code.
     A @('\\x...') escape is turned into a singleton byte list
     with the value of the escape.
     A @('\\u...') escape is turned into a list of 1, 2, or 3 bytes
     that is the UTF-8 encoding of the code point."))
  (escape-case esc
               :single-quote (list (char-code #\'))
               :double-quote (list (char-code #\"))
               :backslash (list (char-code #\\))
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
  :returns (bytes ubyte8-listp
                  :hints (("Goal" :in-theory (enable ubyte8p))))
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
  :returns (bytes ubyte8-listp)
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

(define eval-plain-string-literal ((pstring plain-stringp))
  :returns (val value-resultp)
  :short "Evaluate a plain string literal to a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert the list of string elements to a list of bytes.
     If the resulting bytes exceed 32 in number, it is an error.
     Otherwise, we pad the list with zeros (bytes of value 0) on
     the right to reach 32 bytes,
     and we turn the resulting list of 32 bytes to a 256-bit word,
     interpreting the bytes in big endian form,
     i.e. the first byte contains the most significant bits of the word.
     This evaluation is not described in detail in [Yul],
     but it was explained via discussions on Gitter,
     and [Yul] is being extended with these explanations."))
  (b* ((content (plain-string->content pstring))
       (bytes (eval-string-element-list content))
       ((unless (<= (len bytes) 32))
        (reserrf (list :plain-string-too-long bytes)))
       (bytes (append bytes (repeat (- 32 (len bytes)) 0))))
    (value (bebytes=>nat bytes)))
  :guard-hints
  (("Goal"
    :in-theory (enable ubyte256p
                       bebytes=>nat)
    :use (:instance acl2::bendian=>nat-upper-bound
          (base 256)
          (digits (append
                   (eval-string-element-list
                    (plain-string->content pstring))
                   (repeat (- 32 (len (eval-string-element-list
                                       (plain-string->content pstring))))
                           0))))))
  :hooks (:fix)

  :prepwork

  ((defrulel lemma1
     (implies (ubyte8p x)
              (bytep x))
     :enable bytep)

   (defrulel lemma2
     (implies (ubyte8-listp x)
              (byte-listp x))
     :enable (byte-listp ubyte8-listp)))

  ///

  (defret error-info-wfp-of-eval-plain-string-literal
    (implies (reserrp val)
             (error-info-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-pair-list ((hps hex-pair-listp))
  :returns (bytes ubyte8-listp)
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

(define eval-hex-string-rest-element ((elem hex-string-rest-elementp))
  :returns (val ubyte8p)
  :short "Evaluate an element of hex strings after the first one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This reduces to the evaluation of the pair of hex digits.
     The optional underscore is merely concrete syntactic information,
     retained in the abstract syntax but semantically irrelevant."))
  (eval-hex-pair (hex-string-rest-element->pair elem))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-string-rest-element-list
  ((elems hex-string-rest-element-listp))
  :returns (bytes ubyte8-listp)
  :short "Evaluate a list of element of hex strings after the first one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done element-wise:
     each element is turned into a byte,
     and the order is preserved."))
  (cond ((endp elems) nil)
        (t (cons (eval-hex-string-rest-element (car elems))
                 (eval-hex-string-rest-element-list (cdr elems)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-string-content ((content hex-string-contentp))
  :returns (bytes ubyte8-listp)
  :short "Evaluate the content of a hex string."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return a byte for the first element,
     followed by zero or more bytes for the remaining elements."))
  (b* (((hex-string-content content) content))
    (cons (eval-hex-pair content.first)
          (eval-hex-string-rest-element-list content.rest)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-hex-string-literal ((hstring hex-stringp))
  :returns (val value-resultp)
  :short "Evaluate a hex string literal to a value."
  :long
  (xdoc::topstring
   (xdoc::p
    "We convert the hex pairs to a list of bytes,
     empty if the hex string is empty.
     If the resulting bytes exceed 32 in number, it is an error.
     Otherwise, we pad the list with zeros (bytes of value 0)
     on the right to reach 32 bytes,
     and we turn the resulting list of 32 bytes to a 256-bit word,
     interpreting the bytes in big endian form,
     i.e. the first byte contains the most significant bits of the word.
     This evaluation is not described in detail in [Yul],
     but it was explained via discussions on Gitter,
     and [Yul] is being extended with these explanations."))
  (b* (((hex-string hstring) hstring)
       (bytes (hex-string-content-option-case
               hstring.content
               :some (eval-hex-string-content hstring.content.val)
               :none nil))
       ((unless (<= (len bytes) 32))
        (reserrf (list :hex-string-too-long bytes)))
       (bytes (append bytes (repeat (- 32 (len bytes)) 0))))
    (value (bebytes=>nat bytes)))
  :guard-hints
  (("Goal"
    :in-theory (enable ubyte256p
                       bebytes=>nat)
    :use (:instance acl2::bendian=>nat-upper-bound
                    (base 256)
                    (digits
                     (b* ((bytes
                           (eval-hex-string-content
                            (hex-string-content-option-some->val
                             (hex-string->content hstring)))))
                       (append bytes (repeat (- 32 (len bytes)) 0)))))))
  :hooks (:fix)

  :prepwork

  ((defrulel lemma1
     (implies (ubyte8p x)
              (bytep x))
     :enable bytep)

   (defrulel lemma2
     (implies (ubyte8-listp x)
              (byte-listp x))
     :enable (byte-listp ubyte8-listp)))

  ///

  (defret error-info-wfp-of-eval-hex-string-literal
    (implies (reserrp val)
             (error-info-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-literal ((lit literalp))
  :returns (val value-resultp)
  :short "Evaluate a literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since for now our only values are 256-bit words,
     we evaluate boolean literals to 0 (for false) and 1 (for true),
     viewing the word as an unsigned integer.
     This is not described in [Yul], but it was discussed on Gitter.
     This should apply to at least the EVM dialect of Yul,
     while other dialects that include a boolean type
     may need to evaluate boolean literals differently.
     We will generalize this aspect of our formalization at some point.")
   (xdoc::p
    "A decimal or hexadecimal literal evaluates to the word
     whose unsigned integer value is the number represented by the literal.
     This number must fit in 256 bits, otherwise it is an error.")
   (xdoc::p
    "Plain and hex strings are evaluated as described in
     @(tsee eval-plain-string-literal) and @(tsee eval-hex-string-literal)."))
  (literal-case
   lit
   :boolean (if lit.get (value 1) (value 0))
   :dec-number (if (ubyte256p lit.get)
                   (value lit.get)
                 (reserrf (list :dec-number-too-large lit.get)))
   :hex-number (b* ((num (str::hex-digit-chars-value
                          (hex-digit-list->chars lit.get))))
                 (if (ubyte256p num)
                     (value num)
                   (reserrf (list :hex-number-too-large lit.get))))
   :plain-string (eval-plain-string-literal lit.get)
   :hex-string (eval-hex-string-literal lit.get))
  :hooks (:fix)
  ///

  (defret error-info-wfp-of-eval-literal
    (implies (reserrp val)
             (error-info-wfp val))))
