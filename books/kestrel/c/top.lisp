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
    "This library is based on the "
    (xdoc::ahref "https://www.iso.org/standard/74528.html"
                 "ISO/IEC 9899:2018 specification of C")
    ". In the documentation of this library,
     this standard is referenced as `[C]';
     sections are referenced
     by appending their designations separated by colon,
     e.g. `[C:6.2.6]' references Section 6.2.6;
     paragraphs are referenced
     by further appending their numbers separated by slash,
     e.g. `[C:6.2.5/2]' references Paragraph 2 of Section 6.2.5.
     These square-bracketed references may be used
     as nouns or parenthetically."))
  :order-subtopics (language
                    representation
                    atc
                    c$::syntax-for-tools
                    c2c::transformation-tools
                    pack))
