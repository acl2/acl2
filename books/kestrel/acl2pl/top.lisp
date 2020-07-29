; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "values")
(include-book "translated-terms")
(include-book "packages")
(include-book "functions")
(include-book "programs")
(include-book "primitive-functions")
(include-book "evaluation-states")
(include-book "evaluation")
(include-book "equivalence")
(include-book "interpreter")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ acl2-programming-language
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library about the ACL2 programming language."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 theorem prover includes a programming language,
     which is essentially a subset of Common Lisp.
     ACL2 also includes a logical language,
     which is a superset of a subset of Common Lisp.")
   (xdoc::p
    "This library formalizes certain aspects of
     the syntax and semantics of
     the ACL2 programming language.")
   (xdoc::p
    "The formalization of the ACL2 evaluation semantics in this library
     is currently just the work of this library's author.
     It is not an official descripion of the ACL2 evaluation semantics
     in an analogous sense that "
    (xdoc::ahref "http://www.cs.utexas.edu/users/moore/publications/km97a.pdf"
                 "this techical report")
    " is an official description of the ACL2 logical semantics.
     Refer to manual pages like "
    (xdoc::seetopic "acl2::evaluation" "this one")
    " for an official description of the ACL2 evaluation semantics."))
  :order-subtopics t)
