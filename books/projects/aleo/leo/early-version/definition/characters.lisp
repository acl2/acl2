; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defresult" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ characters
  :parents (abstract-syntax)
  :short "Leo characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Leo, a character is (isomorphic to) a Unicode code point,
     i.e. a number from 0 to @('10FFFF') (hexadecimal).
     In the Unicode standard, not all code points represent valid characters,
     called \"Unicode scalar values\" in the terminology of the standard.
     However, in Leo all code points are considered valid Leo characters."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod char
  :short "Fixtype of Leo characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "We wrap the code point into a one-component product type
     for better encapsulation and abstraction.
     We use an invariant to restrict the number to the prescribed range."))
  ((codepoint nat :reqfix (if (<= codepoint #x10ffff) codepoint 0)))
  :require (<= codepoint #x10ffff)
  :tag :char
  :pred charp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist char-list
  :short "Fixtype of lists of Leo characters."
  :elt-type char
  :true-listp t
  :elementp-of-nil nil
  :pred char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult char-result
  :short "Fixtype of errors and Leo characters."
  :ok char
  :pred char-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult char-list-result
  :short "Fixtype of errors and lists of Leo characters."
  :ok char-list
  :pred char-list-resultp)
