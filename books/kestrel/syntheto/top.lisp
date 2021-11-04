; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "shallow/top")
(include-book "language/top")
(include-book "process-toplevel")
(include-book "base-theory")
(include-book "session-api")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc syntheto
  :parents (kestrel-books)
  :short "An ACL2 library for the Syntheto language."
  :long
  (xdoc::topstring
   (xdoc::p
    "Syntheto is a front-end language for ACL2 and "
    (xdoc::seetopic "apt::apt" "APT")
    ", aimed at a wider range of users than typical ACL2 and APT experts.")
   (xdoc::p
    "Syntheto is being developed by Kestrel Institute,
     in collaboration with Vanderbilt University.")
   (xdoc::p
    "This library includes, both under development,
     a shallow and a deep embedding of Syntheto in ACL2.")
   (xdoc::p
    "The shallow embedding consists of ACL2 macros
     that correspond very closely to the Syntheto abstract syntax.
     These macros can be bidirectionally translated
     to/from non-ACL2 representations of the Syntheto abstract syntax.
     In particular, this will be used in an IDE for Syntheto
     that Vanderbilt University is developing
     in collaboration with Kestrel Institute.")
   (xdoc::p
    "The deep embedding consists of a formalization of
     the syntax and semantics of Syntheto in ACL2.
     It serves to provide a precise definition of the language,
     and may be useful, in the future, when developing APT-like transformations
     that operate directly on the Syntheto language.")))
