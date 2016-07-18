; Processing Unicode Files with ACL2
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>



;; uchar.lisp
;;
;; This file introduces the our representation for Unicode characters and
;; strings.  We simply use integers to represent each code point atomically.

(in-package "ACL2")
(set-verify-guards-eagerness 2)


; Unicode is a popular system for representing abstract characters as integer
; values.  These characters can then be recognized and interpreted by other
; programs, e.g., to be rendered as text for presentation to the user.  The
; CODESPACE is the range of integers used to represent the abstract characters
; of Unicode, and a CODE POINT is a particular integer in the codespace.
;
; The Unicode codespace is 0 to #x10FFFF, inclusive (i.e., 0 to 1,114,111), so
; over a million different characters can be represented.  This is quite larger
; than ASCII or ISO-8859, and so Unicode can precisely represent the characters
; from virtually all languages in the world.  At the present time, most code
; points are not yet assigned, and new versions of the Standard often allocate
; previously unallocated code points in order to support additional languages.
;
; However, because of the way the standard is written, tools that process
; Unicode text do not need to be updated when the standard assigns more
; characters, unless they are going to actually render those characters into
; GLYPHS, i.e., the visual representation that a user will see.  Internally,
; all characters are represented just as integers, so the same algorithms for
; storing, modifying, and so forth will work on future versions of the
; standard.
;
; Here are some of the basic definitions, taken right from the Unicode
; standard, version 8.0.0.


; =============================================================================
; From Section 3.4
;
;   D7: Abstract character: A unit of information used for the organization,
;   control, or representation of textual data.
;
;     - When representing data, the nature of that data is generally symbolic
;     as opposed to some other kind of data (for example, aural or visual).
;     Examples of such symbolic data include letters, ideographs, digits,
;     punctuation,  technical symbols, and dingbats.
;
;     - An abstract character has no concrete form and should not be confused
;     with a glyph.
;
;     - An abstract character does not necessarily correspond to what a user
;     thinks of as a "character" and should not be confused with a grapheme.
;
;     - The abstract characters encoded by the Unicode Standard are known as
;     Unicode abstract characters.
;
;     - Abstract characters not directly encoded by the Unicode Standard can
;     often be represented by the use of combining character sequences.
;
;   D8: Abstract character sequence: An ordered sequence of one or more
;   abstract characters.
;
;   D9: Unicode codespace: A range of integers from 0 to 10FFFF(16).
;
;     - This particular range is defined for the codespace in the Unicode
;     Standard. Other character encoding standards may use other codespaces.
;
;   D10: Code point: Any value in the Unicode codespace.
;
;     - A code point is also known as a code position.
;
;     - See D77 for the definition of code unit.
;
;   D10a: Code point type: Any of the seven fundamental classes of code points
;   in the standard: Graphic, Format, Control, Private-Use, Surrogate,
;   Noncharacter, Reserved.
;
;     - See Table 2-3 for a summary of the meaning and use of each class.
;
;     - For Noncharacter, see also D14 Noncharacter.
;
;     - For Reserved, see also D15 Reserved code point.
;
;     - For Private-Use, see also D49 Private-use code point.
;
;     - For Surrogate, see also D71 High-surrogate code point and D73
;     Low-surrogate code point.
;
;   D11: Encoded character: An association (or mapping) between an abstract
;   character and a code point.
;
;     - An encoded character is also referred to as a coded character.
;
;     - While an encoded character is formally defined in terms of the mapping
;     between an abstract character and a code point, informally it can be
;     thought of as an abstract character taken together with its assigned
;     code point.
;
;     - Occasionally, for compatibility with other standards, a single
;     abstract character may correspond to more than one code point - for example,
;     [symbol I can't type in ascii] corresponds both to U+00C5 (LATIN CAPITAL
;     LETTER A WITH RING ABOVE) and to U+212B (ANGSTROM SIGN).
;
;     - A single abstract character may also be represented by a sequence of
;     code points - for example, LATIN CAPITAL LETTER G WITH ACUTE may be
;     represented by the sequence <U+0047 LATIN CAPITAL LETTER G, U+0301
;     COMBINING ACUTE ACCENT>, rather than being mapped to a single code point.
;
; =============================================================================


; Now, Unicode is quite a bit more complicated than ASCII.  After all, in
; ASCII, every character takes only one byte.  This means you don't have to
; worry about byte order when writing to files or transmitting across networks,
; and so forth.  Similarly, there is little worry about the size of an ASCII
; text file: each character just takes a single byte.
;
; Because Unicode characters are larger, there has been quite a lot of thought
; about how characters should be encoded when they are stored in files, sent
; across the network, and even represented in memory.  As a result, there are
; three supported Unicode Encoding FORMS and seven supported Unicode Encoding
; SCHEMES.  The difference is subtle, but basically an encoding FORM doesn't
; have to worry about serialization for network/file transfer, and an encoding
; SCHEME does.
;
; Let's begin with the Unicode Encoding FORMS since they are simpler.  Here
; are the relevant parts of the standard:


; =============================================================================
; From Section 3.9
;
;   The Unicode Standard supports three character encoding forms: UTF-32,
;   UTF-16, and UTF-8. Each encoding form maps the Unicode code points
;   U+0000..U+D7FF and U+E000..U+10FFFF to unique code unit sequences.  The
;   size of the code unit is specified for each encoding form.  This section
;   presents the formal definition of each of these encoding forms.
;
;   D76: Unicode scalar value: Any Unicode code point except high-surrogate and
;   low-surrogate code points.
;
;     - As a result of this definition, the set of Unicode scalar values
;     consists of the ranges 0 to D7FF(16) and E000(16) to 10FFFF(16), inclusive.
;
;   D77: Code unit: The minimal bit combination that can represent a unit
;   of encoded text for processing or interchange.
;
;     - Code units are particular units of computer storage.  Other character
;     encoding standards typically use code units defined as 8-bit units - that is,
;     octets.  The Unicode Standard uses 8-bit code units in the UTF-8 encoding
;     form, 16-bit code units in the UTF-16 encoding form, and 32-bit code
;     units in the UTF-32 encoding form.
;
;     - A code unit is also referred to as a code value in the information
;     industry.
;
;     - In the Unicode Standard, specific values of some code units cannot be
;     used to represent an encoded character in isolation.  This restriction
;     applies to isolated surrogate code units in UTF-16 and to the bytes 80-FF
;     in UTF-8.  Similar restrictions apply for the implementations of other
;     character encoding standards; for example, the bytes 81-9F, E0-FC in SJIS
;     (Shift-JIS) cannot represent an encoded character by themselves.
;
;     - For information on use of wchar_t or other programming language types to
;     represent Unicode code units, see "ANSI/ISO C wchar_t" in Section 5.2,
;     Programming Languages and Data Types.
;
;   D78: Code unit sequence: An ordered sequence of one or more code units.
;
;     - When the code unit is an 8-bit unit, a code unit sequence may also be
;     referred to as a byte sequence.
;
;     - A code unit sequence may consist of a single code unit.
;
;     - In the context of programming languages, the value of a string data
;     type basically consists of a code unit sequence.  Informally, a code unit
;     sequence is itself just referred to as a string, and a byte sequence is
;     referred to as a byte string.  Care must be taken in making this
;     terminological equivalence, however, because the formally defined concept
;     of a string may have additional requirements or complications in
;     programming languages.  For example, a string is defined as a pointer to
;     char in the C language and is conventionally terminated with a NULL
;     character.  In object-oriented languages, a string is a complex object,
;     with associated methods, and its value may or may not consist of merely a
;     code unit sequence.
;
;     - Depending on the structure of a character encoding standard, it may be
;     necessary to use a code unit sequence (of more than one unit) to
;     represent a single encoded character.  For example, the code unit in SJIS
;     is a byte: encoded characters such as "a" can be represented with a
;     single byte in SJIS, whereas ideographs require a sequence of two code
;     units.  The Unicode Standard also makes use of code unit sequences whose
;     length is greater than one code unit.
;
;
;   D79: A Unicode encoding form assigns each Unicode scalar value to a unique
;   code unit sequence.
;
;     - For historical reasons, the Unicode encoding forms are also referred to
;     as Unicode (or UCS) transformation formats (UTF).  That term is actually
;     ambiguous between its usage for encoding forms and encoding schemes.
;
;     - The mapping of the set of Unicode scalar values to the set of code unit
;     sequences for a Unicode encoding form is one-to-one.  This property
;     guarantees that a reverse mapping can always be derived.  Given the
;     mapping of any Unicode scalar value to a particular code unit sequence
;     for a given encoding form, one can derive the original Unicode scalar
;     value unambiguously from that code unit sequence.
;
;     - The mapping of the set of Unicode scalar values to the set of code unit
;     sequences for a Unicode encoding form is not onto.  In other words, for
;     any given encoding form, there exist code unit sequences that have no
;     associated Unicode scalar value.
;
;     - To ensure that the mapping for a Unicode encoding form is one-to-one,
;     all Unicode scalar values, including those corresponding to noncharacter
;     code points and unassigned code points, must be mapped to unique code
;     unit sequences.  Note that this requirement does not extend to
;     high-surrogate and low-surrogate code points, which are excluded by
;     definition from the set of Unicode scalar values.
;
;   D80: Unicode string: A code unit sequence containing code units of a
;   particular Unicode encoding form.
;
;     - In the rawest form, Unicode strings may be implemented simply as arrays
;     of the appropriate integral data type, consisting of a sequence of code
;     units lined up one immediately after the other.
;
;     - A single Unicode string must contain only code units from a single
;     Unicode encoding form.  It is not permissible to mix forms within a
;     string.
;
;   D81: Unicode 8-bit string: A Unicode string containing only UTF-8 code
;   units.
;
;   D82: Unicode 16-bit string: A Unicode string containing only UTF-16 code
;   units.
;
;   D83: Unicode 32-bit string: A Unicode string containing only UTF-32 code
;   units.
;
;   D84: Ill-formed: A Unicode code unit sequence that purports to be in a Unicode
;   encoding form is called ill-formed if and only if it does not follow the
;   specification of that Unicode encoding form.
;
;     - Any code unit sequence that would correspond to a code point outside
;     the defined range of Unicode scalar values would, for example, be ill-formed.
;
;     - UTF-8 has some strong constraints on the possible byte ranges for
;     leading and trailing bytes.  A violation of those constraints would
;     produce a code unit sequence that could not be mapped to a Unicode
;     scalar value, resulting in an ill-formed code unit sequence.
;
;   D84a: Ill-formed code unit subsequence: A non-empty subsequence of a
;   Unicode code unit sequence X which does not contain any code units which
;   also belong to any minimal well-formed subsequence of X.
;
;     - In other words, an ill-formed code unit subsequence cannot overlap with
;     a minimal well-formed subsequence.
;
;   D85: Well-formed: A Unicode code unit sequence that purports to be in a
;   Unicode encoding form is called well-formed if and only if it does follow
;   the specification of that Unicode encoding form.
;
;   D85a: Minimal well-formed code unit subsequence: A well-formed Unicode code
;   unit sequence that maps to a single Unicode scalar value.
;
;     - For UTF-8, see the specification in D92 and Table 3-7.
;
;     - For UTF-16, see the specification in D91.
;
;     - For UTF-32, see the specification in D90.
;
;   A well-formed Unicode code unit sequence can be partitioned into one or
;   more minimal well-formed code unit sequences for the given Unicode encoding
;   form.  Any Unicode code unit sequence can be partitioned into subsequences
;   that are either well-formed or ill-formed.  The sequence as a whole is
;   well-formed if and only if it contains no ill-formed subsequence.  The
;   sequence as a whole is ill-formed if and only if it contains at least one
;   ill-formed subsequence.
;
;   D86: Well-formed UTF-8 code unit sequence: A well-formed Unicode code
;   unit sequence of UTF-8 code units.
;
;     - The UTF-8 code unit sequence <41 C3 B1 42> is well-formed, because it
;     can be partitioned into subsequences, all of which match the
;     specification for UTF-8 in Table 3-7.  It consists of the following
;     minimal well-formed code unit subsequences: <41>, <C3 B1>, and <42>.
;
;     - The UTF-8 code unit sequence <41 C2 C3 B1 42> is ill-formed, because it
;     contains one ill-formed subsequence.  There is no subsequence for the C2
;     byte which matches the specification for UTF-8 in Table 3-7.  The code
;     unit sequence is partitioned into one minimal well-formed code unit
;     subsequence, <41>, followed by one ill-formed code unit subsequence,
;     <C2>, followed by two minimal well-formed code unit subsequences, <C3 B1>
;     and <42>.
;
;     - In isolation, the UTF-8 code unit sequence <C2 C3> would be ill-formed,
;     but in the context of the UTF-8 code unit sequence <41 C2 C3 B1 42>,
;     <C2 C3> does not constitute an ill-formed code unit subsequence, because
;     the C3 byte is actually  the  first  byte  of  the  minimal well-formed
;     UTF-8 code unit subsequence <C3 B1>. Ill-formed code unit subsequences do
;     not overlap with minimal well-formed code unit subsequences.
;
;   D87: Well-formed UTF-16 code unit sequence: A well-formed Unicode code
;   unit sequence of UTF-16 code units.
;
;   D88: Well-formed UTF-32 code unit sequence: A well-formed Unicode code
;   unit sequence of UTF-32 code units.
;
;   D89: In a Unicode encoding form: A Unicode string is said to be in a
;   particular Unicode encoding form if and only if it consists of a
;   well-formed Unicode code unit sequence of that Unicode encoding form.
;
;     - A Unicode string consisting of a well-formed UTF-8 code unit sequence
;     is said to be in UTF-8.  Such a Unicode string is referred to as a valid
;     UTF-8 string, or a UTF-8 string for short.
;
;     - A Unicode string consisting of a well-formed UTF-16 code unit sequence
;     is said to be in UTF-16.  Such a Unicode string is referred to as a valid
;     UTF-16 string, or a UTF-16 string for short.
;
;     - A Unicode string consisting of a well-formed UTF-32 code unit sequence
;     is said to be in UTF-32.  Such a Unicode string is referred to as a valid
;     UTF-32 string, or a UTF-32 string for short.
;
;   Unicode strings need not contain well-formed code unit sequences under
;   all conditions.  This is equivalent to saying that a particular Unicode
;   string need not be in a Unicode encoding form.
;
;     - For example, it is perfectly reasonable to talk about an operation that
;     takes the two Unicode 16-bit strings, <004D D800> and <DF02 004D>, each
;     of which contains an ill-formed UTF-16 code unit sequence, and
;     concatenates them to form another Unicode string <004D D800 DF02 004D>,
;     which contains a well-formed UTF-16 code unit sequence.  The first two
;     Unicode strings are not in UTF-16, but the resultant Unicode string is.
;
;     - As another example, the code unit sequence <C0 80 61 F3> is a Unicode
;     8-bit string, but does not consist of a well-formed UTF-8 code unit
;     sequence.  That code unit sequence could not result from the
;     specification of the UTF-8 encoding form and is thus ill-formed.  (The
;     same code unit sequence could, of course, be well-formed in the context of
;     some other character encoding standard using 8-bit code units, such as
;     ISO/IEC 8859-1, or vendor code pages.)
;
;   If a Unicode string purports to be in a Unicode encoding form, then it must
;   not contain any ill-formed code unit subsequence.
;
;   If a process which verifies that a Unicode string is in a Unicode encoding
;   form encounters an ill-formed code unit subsequence in that string, then it
;   must not identify that string as being in that Unicode encoding form.
;
;   A process which interprets a Unicode string must not interpret any
;   ill-formed code unit subsequences in the string as characters.  (See
;   conformance clause C10.) Furthermore, such a process must not treat any
;   adjacent well-formed code unit sequences as being part of those ill-formed
;   code unit sequences.
;
; =============================================================================

; What does all this mean to us.  Basically, Unicode encoding forms are just
; concerned with how we represent Unicode strings in memory.

; This is all well and good, but in ACL2 we don't really have much ability to
; tightly pack characters into byte arrays.  Instead, what we'll do is just
; represent Unicode scalar values as integers.  Because "Unicode scalar value"
; is a lot to type, we will call our recognizer uchar? instead.

(defmacro in-range? (x low high)
  "Check if x is between low and high, inclusive."
  `(and (<= ,low ,x)
        (<= ,x ,high)))

(defun uchar? (x)
  "Recognizer for Unicode scalar values."
  (and (integerp x)
       (or (in-range? x 0 #xD7FF)
           (in-range? x #xE000 #x10FFFF))))

(defthm uchar-range
  (implies (uchar? x)
           (and (integerp x)
                (<= 0 x)
                (<= x #x10FFFF)))
  :rule-classes ((:rewrite)
                 (:forward-chaining)))

(defthm uchar?-signed-byte-29
  (implies (uchar? x)
           (signed-byte-p 29 x))
  :hints(("Goal" :in-theory (enable signed-byte-p))))

(in-theory (disable uchar?))



; Furthermore, we'll just represent code unit sequences as as lists of uchars.
; This representation is really inefficient as far as memory goes, and in the
; future, we might want to consider expanding on this definition and being more
; aggressive with bit operations to compact our memory usage.  But, this is
; very simple.
;
; Although Unicode strings are actually defined by the spec with respect to a
; particular encoding form, we will call our code unit sequence recognizer
; ustring?, in recognition of the fact that the ONLY encoding form we will
; internally support is this uchar-based system, so WE have only one concept
; of a Unicode string.

(defun ustring? (x)
  "Recognizer for Unicode code unit sequences."
  (if (atom x)
      (null x)
    (and (uchar? (car x))
         (ustring? (cdr x)))))

(defthm ustring-true-list
  (implies (ustring? x)
           (true-listp x)))

(defthm cdr-preserves-ustring
  (implies (ustring? x)
           (ustring? (cdr x))))




; One problem with supporting Unicode in ACL2 is that fms and so forth are all
; based on ASCII, so there is not a very easy way to view a Unicode string.
; For example, it isn't very obvious that (104 101 108 108 111) is hello in
; Unicode, and it would be quite painful to try to actually read Unicode output
; in this format.
;
; So, we provide some useful functions.
;
;  (ascii x) converts a Unicode string into ASCII.  Note that since Unicode
;  contains characters that ASCII cannot represent, this translation is not
;  perfect, and non-ASCII characters will be turned into question marks.
;  Still, it is useful for debugging purposes.
;
;    Example: (ascii '(104 101 108 108 111)) -> "hello"
;
;  (ustring x) converts an ASCII string into Unicode.  This translation is
;  always exact, since Unicode subsumes ASCII.
;
;    Example: (ustring "hello") -> (104 101 108 108 111)

(defun uchar=>char (x)
  "Convert a Unicode character into an ASCII character.
  Note that any character which is not ASCII-compatible will be turned
  into a question mark."
  (declare (xargs :guard (uchar? x)))
  (declare (type (signed-byte 29) x))
  (if (< x 256)
      (code-char x)
    #\?))

(defun ustring=>charlist (x)
  "Convert a Unicode string into an ASCII character list.
  Note that any characters which are not ASCII-compatible will be turned
  into question marks."
  (declare (xargs :guard (ustring? x)
                  :guard-hints(("Goal" :in-theory (disable signed-byte-p)))))
  (if (atom x)
      nil
    (cons (uchar=>char (car x))
          (ustring=>charlist (cdr x)))))

(defun ascii (x)
  "Convert a Unicode string into an ASCII string.
  Note that any characters which are not ASCII-compatible will be turned
  into question marks."
  (declare (xargs :guard (ustring? x)))
  (coerce (ustring=>charlist x) 'string))

(defun charlist=>ustring (x)
  "Convert an ASCII character list into a Unicode string."
  (declare (xargs :guard (character-listp x)))
  (if (atom x)
      nil
    (cons (char-code (car x))
          (charlist=>ustring (cdr x)))))

(defun ustring (x)
  "Convert an ASCII string into a Unicode string."
  (declare (xargs :guard (stringp x)))
  (charlist=>ustring (coerce x 'list)))
