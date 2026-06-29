; Documentation for the Unicode library
;
; License: An MIT/X11-style license; see uchar.lisp.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "uchar")
(include-book "utf8-encode")
(include-book "utf8-decode")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode
  :parents (acl2)
  :short "An ACL2 library for processing Unicode text and UTF-8 byte sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library formalizes the
     core of the Unicode 8.0.0 standard for representing Unicode
     characters as natural numbers (@(tsee uchar?)), representing
     Unicode strings as lists of natural numbers (@(tsee ustring?)),
     and translating between Unicode characters/strings and UTF-8
     byte sequences.")
   (xdoc::p
    "A Unicode code point is a number in the range @('[0, #x10FFFF]').
     A Unicode scalar value is any code point in that range
     but not in the surrogate subrange @('[#xD800, #xDFFF]').
     In general, when we talk about Unicode characters, we mean
     Unicode scalar values.  Sometimes, we refer to code points
     even when we mean to exclude the surrogate subrange.
     Generally the meaning is clear since the type/guard is @(tsee uchar?).")
   (xdoc::p
    "A user-perceived character can often require more than
     one Unicode character.  For example, some letters with accent marks
     require two characters, and some emojis can be
     combined with gender or color markers.  This library
     is concerned with Unicode characters and sequences of Unicode characters,
     and does not yet handle grapheme clusters (sequences of
     Unicode characters that a user perceives as a single character).")
   (xdoc::p
    "The library includes:")
   (xdoc::ul
    (xdoc::li
     "Recognizers for Unicode scalar values and Unicode strings:
      @(tsee uchar?), @(tsee ustring?).")
    (xdoc::li
     "Functions for encoding into UTF-8 byte sequences:
      @(tsee uchar=>utf8) for a single code point and
      @(tsee ustring=>utf8) for a list of code points.")
    (xdoc::li
     "Functions for decoding UTF-8 byte sequences:
      @(tsee utf8-partition) to detect whether a byte sequence is a
      well-formed UTF-8 character stream and how it is sliced into
      individual character byte groups, and @(tsee utf8=>ustring) to
      convert valid UTF-8 byte sequences back to code points.")
    (xdoc::li
     "Round-trip theorems and distribution lemmas connecting the
      encoder and the decoder."))
   (xdoc::p
    "The library lives in the @(see community-books) directory
     @('books/unicode/').  See the individual files for additional
     intermediate definitions and theorems.")
   (xdoc::p
    "The Unicode 8.0.0 standard is available at
     @('https://www.unicode.org/versions/Unicode8.0.0/').  The Core
     Specification (a multi-chapter PDF) is the primary reference;
     for example, Chapter 3 (Conformance) contains the UTF-8
     bit-distribution table referenced by the encoder and decoder
     documentation as ``Table 3-6''."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc uchar?
  :parents (unicode)
  :short "Recognizer for Unicode characters (scalar values)."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(uchar? x) &rarr; bool</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; Any ACL2 value.</dd>
<dt>Returns</dt>
<dd><tt>bool</tt> &mdash; @('t') if @('x') is a Unicode scalar value,
otherwise @('nil').</dd>
</dl></box>"
   (xdoc::p
    "@('(uchar? x)') is non-@('nil') exactly when @('x') is a natural number in
     either @('[0, #xD7FF]') or @('[#xE000, #x10FFFF]').  Together,
     these ranges are the Unicode scalar values: code points within the
     codespace excluding the surrogate range @('[#xD800, #xDFFF]').
     The surrogate range is reserved for use with the UTF-16 encoding form;
     the code points in it are not considered valid Unicode characters.")
   (xdoc::p
    "Internally we represent a Unicode character atomically as a
     natural number code point.")
   (xdoc::p "Definition:")
   "@(def uchar?)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc ustring?
  :parents (unicode)
  :short "Recognizer for Unicode strings (lists of Unicode characters)."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(ustring? x) &rarr; bool</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; Any ACL2 value.</dd>
<dt>Returns</dt>
<dd><tt>bool</tt> &mdash; @('t') if @('x') is a true list of @(tsee uchar?)
values, otherwise @('nil').</dd>
</dl></box>"
   (xdoc::p
    "@('(ustring? x)') is non-@('nil') exactly when @('x') is a true
     list whose every element satisfies @(tsee uchar?).")
   (xdoc::p
    "Other Unicode encoding forms (UTF-8, UTF-16, UTF-32) are
     produced or consumed by encoding and decoding functions but
     are not used here as a representation of Unicode.")
   (xdoc::p "Definition:")
   "@(def ustring?)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc uchar=>utf8
  :parents (unicode)
  :short "Encode a single Unicode code point as a UTF-8 byte sequence."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(uchar=&gt;utf8 x) &rarr; bytes</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; A Unicode code point.<br/>&nbsp;&nbsp;&nbsp;&nbsp;<color rgb='#606060'>Guard @('(uchar? x)').</color></dd>
<dt>Returns</dt>
<dd><tt>bytes</tt> &mdash; The 1-, 2-, 3-, or 4-byte UTF-8 encoding of
@('x'), as a list of unsigned 8-bit bytes.</dd>
</dl></box>"
   (xdoc::p
    "@('(uchar=>utf8 x)') takes a @(tsee uchar?) @('x') and returns the
     1-, 2-, 3-, or 4-byte UTF-8 representation of @('x') as a list
     of unsigned 8-bit bytes, following Table 3-6 of the Unicode
     standard.")
   (xdoc::p
    "ASCII code points (@('[0, #x7F]')) encode to a single byte equal
     to the code point itself.  Larger code points encode to 2-4 bytes
     with the standard UTF-8 leading-byte and continuation-byte
     patterns.")
   (xdoc::p
    "See @(tsee ustring=>utf8) for the lifting to a list of code
     points.")
   (xdoc::p "Definition:")
   "@(def uchar=>utf8)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc ustring=>utf8
  :parents (unicode)
  :short "Encode a Unicode string as a UTF-8 byte sequence."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(ustring=&gt;utf8 x) &rarr; bytes</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; A Unicode string (list of code points).<br/>&nbsp;&nbsp;&nbsp;&nbsp;<color rgb='#606060'>Guard @('(ustring? x)').</color></dd>
<dt>Returns</dt>
<dd><tt>bytes</tt> &mdash; The UTF-8 encoding of @('x'), as a list of
unsigned 8-bit bytes.</dd>
</dl></box>"
   (xdoc::p
    "@('(ustring=>utf8 x)') takes a @(tsee ustring?) @('x') and produces
     the concatenation of the UTF-8 encodings of its individual code
     points (see @(tsee uchar=>utf8)).  The result is a list of
     unsigned 8-bit bytes.")
   (xdoc::p
    "Encoding distributes over @(tsee append) on Unicode strings; see
     @('ustring=>utf8-of-append-when-ustrings').")
   (xdoc::p "Definition:")
   "@(def ustring=>utf8)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc utf8-partition
  :parents (unicode)
  :short "Find the sizes in bytes of Unicode characters in a UTF-8-encoded byte list."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(utf8-partition x) &rarr; (mv successp sizes)</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; A list of 8-bit natural numbers.</dd>
<dt>Returns</dt>
<dd><tt>successp</tt> &mdash; Non-@('nil') iff @('x') is a well-formed
UTF-8 byte sequence.</dd>
<dd><tt>sizes</tt> &mdash; When @('successp') is non-@('nil'), a list of
natural numbers (each in 1-4) giving the sizes of consecutive character
byte groups; otherwise @('nil').</dd>
</dl></box>"
   (xdoc::p
    "@('(utf8-partition x)') returns @('(mv successp sizes)').  When
     @('successp') is non-@('nil'), @('sizes') is a list of natural
     numbers (each in 1-4) such that grouping @('x') into consecutive
     subsequences of those sizes yields a valid sequence of UTF-8
     character byte groups.  When @('successp') is @('nil'),
     @('sizes') is @('nil').")
   (xdoc::p
    "The function is the basis for the decoder @(tsee utf8=>ustring),
     and its success predicate @('(mv-nth 0 (utf8-partition x))') is
     the natural well-formedness condition on UTF-8 byte sequences.")
   (xdoc::p "Definition:")
   "@(def utf8-partition)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc utf8=>ustring
  :parents (unicode)
  :short "Decode a UTF-8 byte sequence to a Unicode string (list of nats)."
  :long
  (xdoc::topstring
   "<box><dl>
<dt>Signature</dt>
<dt><code>(utf8=&gt;ustring x) &rarr; result</code></dt>
<dt>Arguments</dt>
<dd><tt>x</tt> &mdash; A list of unsigned 8-bit bytes.</dd>
<dt>Returns</dt>
<dd><tt>result</tt> &mdash; A @(tsee ustring?) when @('x') is well-formed
UTF-8, otherwise the symbol @('fail').</dd>
</dl></box>"
   (xdoc::p
    "@('(utf8=>ustring x)') takes a list of unsigned 8-bit bytes
     @('x') and returns the corresponding @(tsee ustring?) when @('x')
     is a well-formed UTF-8 byte sequence (i.e., when
     @('(mv-nth 0 (utf8-partition x))') is non-@('nil')).  When
     @('x') is not well-formed, the function returns the symbol
     @('fail').")
   (xdoc::p
    "Together with @(tsee ustring=>utf8) this gives a round-trip
     encoding/decoding pair: see
     @('utf8=>ustring-of-ustring=>utf8') and
     @('ustring=>utf8-of-utf8=>ustring') for the two directions.")
   (xdoc::p
    "Decoding distributes over @(tsee append) on validly partitionable
     byte sequences; see
     @('utf8=>ustring-of-append-when-utf8-partition').")
   (xdoc::p "Definition:")
   "@(def utf8=>ustring)"))
