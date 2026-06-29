; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "library-extensions")
(include-book "concrete-syntax")
(include-book "abstract-syntax")
(include-book "parsing-and-printing")
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "monomorphize")
(include-book "monomorphize-file")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ remora
  :parents (acl2::projects acl2::kestrel-books)
  :short "An ACL2 library for Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "Remora is a programming language, under development,
     that features parallelism and rank polymorphism,
     i.e. the ability of code to lift
     from arrays of lower ranks to arrays of higher ranks,
     where an `array' is a regular arrangement of homogeneous values
     of an arbitrary number of dimensions
     (0 for scalars, 1 for vectors, 2 for matrices, etc.).")
   (xdoc::p
    "This library is based on the following sources:")
   (xdoc::ul
    (xdoc::li
     (xdoc::ahref
      "https://arxiv.org/abs/1907.00509v1"
      "``The Semantics of Rank Polymorphism''")
     " by Justin Slepak, Olin Shivers, and Panagiotis Manolios:
      an arXiv paper submitted to the Journal of Functional Programming.
      We reference this as `[arxiv]' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://link.springer.com/chapter/10.1007/978-3-642-54833-8_3"
      "``An Array-Oriented Language with Static Rank Polymorphism''")
     " by Justin Slepak, Olin Shivers, and Panagiotis Manolios:
      a conference paper published at ESOP, available "
     (xdoc::ahref
      "https://www.khoury.northeastern.edu/home/pete/research/esop-2014.html"
      "here")
     ". We reference this as `[esop]' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://arxiv.org/abs/1912.13451"
      "``Introduction to Rank-polymorphic Programming in Remora (Draft)''")
     " by Olin Shivers, Justin Slepak, and Panagiotis Manolios:
      a tutorial on Remora.
      We reference this as `[tutor]' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://www.khoury.northeastern.edu/~jrslepak/Dissertation.pdf"
      "``A Typed Programming Language - The Semantics of Rank Polymorphism''")
     " by Justin Slepak:
      PhD dissertation.
      We reference this as `[thesis]' in the documentation.")
    (xdoc::li
     "The "
     (xdoc::ahref
      "https://github.com/remora-lang/remora"
      "implementation of Remora on GitHub")
     ", which includes an interpreter and compiler.
      This implementation is work in progress.
      We reference this as `[impl]' in the documentation."))
   (xdoc::p
    "Since [impl] is more recent than the other sources,
     and [impl] is under active development,
     it is the main source,
     and the one we follow in case of discrepancies.
     However, the other sources contain information (e.g. typing rules)
     not directly and explicitly present in [impl],
     and thus they are still quite important.
     [arxiv] and [thesis] are quite aligned,
     with the latter being probably slightly more up to date.
     [esop] has some differences, but it is older.
     Thus, we generally refer to [thesis], besides [impl].")
   (xdoc::p
    "This ACL2 library is work in progress towards building
     formalizations and tools for Remora."))
  :order-subtopics (library-extensions
                    concrete-syntax
                    abstract-syntax
                    parsing-and-printing
                    static-semantics
                    dynamic-semantics
                    monomorphize-prog))
