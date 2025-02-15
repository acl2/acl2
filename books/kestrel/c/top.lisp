; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2024 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "language/top")
(include-book "representation/top")
(include-book "atc/top")
(include-book "syntax/top")
(include-book "transformation/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ c
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library contains:")
   (xdoc::ul
    (xdoc::li
     "A formalization of (a subset of) the C language.
      This is a deep embedding of C in ACL2.")
    (xdoc::li
     "A representation of (a subset of) the C language constructs in ACL2.
      This is a shallow embedding of C in ACL2.")
    (xdoc::li
     "A proof-generating C code generator for ACL2.
      This recognizes, and translates to C,
      the shallowly embedded ACL2 representation of C constructs,
      and generates proofs based on the deep embedding.")
    (xdoc::li
     "A tool-oriented syntax of C."))
   (xdoc::p
    "The library is work in progress.")
   (xdoc::p
    "This library is based on:")
   (xdoc::ul
    (xdoc::li
     (xdoc::ahref "https://www.iso.org/standard/82075.html"
                  "ISO/IEC 9899:2024")
     ", i.e. the C23 standard.")
    (xdoc::li
     (xdoc::ahref "https://www.iso.org/standard/74528.html"
                  "ISO/IEC 9899:2018")
     ", i.e. the C17 standard.")
    (xdoc::li
     "The "
     (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/"
                  "GCC Manual for the current development")
     "."))
   (xdoc::p
    "In the documentation of this library,
     these source are referenced as `[C23]', `[C17]', and `[GCC];
     sections are referenced
     by appending their designations separated by colon,
     e.g. `[C17:6.2.6]' references Section 6.2.6 of [C17];
     paragraphs are referenced
     by further appending their numbers separated by slash,
     e.g. `[C17:6.2.5/2]' references Paragraph 2 of Section 6.2.5 of [C17].
     These square-bracketed references may be used
     as nouns or parenthetically.
     In the case of [GCC], we also give URL links,
     which, given their form, may be useful to locate
     documentation that has moved or otherwise changed,
     given that [GCC] is a live document;
     an example is "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/C-Extensions.html"
                 "[GCC:6]")
    ", which currently refers to Section 6,
     titled `Extensions to the C Language Family',
     and whose URL includes @('C-Extensions.html').")
   (xdoc::p
    "Although GCC provides extensions to the ISO/IEC standard,
     they are sufficiently prevalent and important that
     we need to take them into account
     for our library of C to be of practical use.
     But in the documentation of this ACL2 library,
     we always clearly distinguish between
     standard C and GCC extensions."))
  :order-subtopics (language
                    representation
                    atc
                    c$::syntax-for-tools
                    c2c::transformation-tools
                    pack))
