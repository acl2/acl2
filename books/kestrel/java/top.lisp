; Java Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "language/top")
(include-book "aij/top")
(include-book "atj/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ java
  :parents (acl2::kestrel-books acl2::projects)
  :short "An ACL2 library for Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this library contains:")
   (xdoc::ul
    (xdoc::li
     "A formalization in ACL2 of some aspects of the Java language.")
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
     "The "
     (xdoc::ahref "https://docs.oracle.com/javase/specs/jls/se21/html"
                  "Java language specification")
     ", referenced as `[JLSe]' in the documentation of this library,
      where `e' is the Edition, e.g. `[JLS21]' for Java SE 21 Edition.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g. `[JLS21:4.2]' references Section 4.2 of [JLS21].")
    (xdoc::li
     "The "
     (xdoc::ahref "https://docs.oracle.com/javase/specs/jvms/se21/html"
                  "Java Virtual Machine specification")
     ", referenced as `[JVMSe]' in the documentation of this library,
      where `e' is the Edition, e.g. `[JVMS21]' for Java SE 21 Edition.
      Chapters and sections are referenced
      by appending their designations separated by colon,
      e.g. `[JVMS21:5.5]' references Section 5.5 of [JVMS21].")
    (xdoc::li
     "The "
     (xdoc::ahref "https://docs.oracle.com/en/java/javase/21/docs/api"
                  "Java API specification")
     ", referenced as `[JAPISe]' in the documentation of this library
      where `e' is the Edition, e.g. `[JAPIS21]' for Java SE 21 Edition."))
   (xdoc::p
    "These square-bracketed references may be used
     as nouns or parenthentically.")
   (xdoc::p
    "The documentation of this library may use references
     for different Java Editions, e.g. [JLS21] and [JLS20].
     Ideally, all the references should be for the latest Edition,
     but in practice it may take time to update them
     when a new Java Edition is released (which happens relatively often);
     the references need to be double-checked for each new Edition,
     as things may change.
     By always using the Edition number in the references,
     we at least guarantee their accuracy."))
  :order-subtopics (language
                    aij
                    atj))
