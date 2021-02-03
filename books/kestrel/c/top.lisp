; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "language/top")
(include-book "atc/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ c
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a library that is being populated with:")
   (xdoc::ul
    (xdoc::li
     "A formalization of (some aspects of) the C language.")
    (xdoc::li
     "A C code generator for ACL2."))
   (xdoc::p
    "The library may also extended with
     more C-related formalizations and tools.")
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
  :order-subtopics t)
