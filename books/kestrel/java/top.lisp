; Java Library
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the JAVA topic below:
(include-book "aij/top")
(include-book "atj/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ java
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Java."
  :long
  (xdoc::topapp
   (xdoc::p
    "Currently this library contains:")
   (xdoc::ul
    (xdoc::li
     "A deep embedding of ACL2 in Java.")
    (xdoc::li
     "A Java code generator for ACL2."))
   (xdoc::p
    "It is expected that this library will be extended with more
     Java-related formalizations and tools.")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/specs/jls/se10/html\"
      >Java language specification</a>,
      referenced as `[JLS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JLS:4.2]' references Section 4.2.")
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/specs/jvms/se10/html\"
      >Java Virtual Machine specification</a>,
      referenced as `[JVMS]' in the documentation of this library.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g.
      `[JVMS:5.5]' references Section 5.5.")
    (xdoc::li
     "The <a href=\"https://docs.oracle.com/javase/10/docs/api\"
      >Java API specification</a>,
      referenced as `[JAPIS]' in the documentation of this library."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically."))
  :order-subtopics t)
