; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "grammar")
(include-book "abstract-syntax")
(include-book "static-semantics")

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
     (0 for scalars, 1 for vectors, 2 for matrices, etc.).
     Remora is described in the following publications:")
   (xdoc::ul
    (xdoc::li
     (xdoc::ahref
      "https://arxiv.org/abs/1907.00509v1"
      "``The Semantics of Rank Polymorphism''")
     " by Justin Slepak, Olin Shivers, and Panagiotis Manolios:
      an arXiv paper submitted to the Journal of Functional Programming.
      We refer to this as `arXiv paper' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://link.springer.com/chapter/10.1007/978-3-642-54833-8_3"
      "``An Array-Oriented Language with Static Rank Polymorphism''")
     " by Justin Slepak, Olin Shivers, and Panagiotis Manolios:
      a conference paper published at ESOP, available "
     (xdoc::ahref
      "https://www.khoury.northeastern.edu/home/pete/research/esop-2014.html"
      "here")
     ". We refer to this as `ESOP paper' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://arxiv.org/abs/1912.13451"
      "``Introduction to Rank-polymorphic Programming in Remora (Draft)''")
     " by Olin Shivers, Justin Slepak, and Panagiotis Manolios:
      a tutorial on Remora.
      We refer to this as `tutorial' in the documentation.")
    (xdoc::li
     (xdoc::ahref
      "https://www.khoury.northeastern.edu/~jrslepak/Dissertation.pdf"
      "``A Typed Programming Language - The Semantics of Rank Polymorphism''")
     " by Justin Slepak:
      PhD dissertation.
      We refer to this as `dissertation' in the documentation."))
   (xdoc::p
    "This ACL2 library is work in progress towards building
     formalizations and tools for Remora."))
  :order-subtopics (grammar
                    abstract-syntax
                    static-semantics))
