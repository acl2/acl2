; Standard Typed Alists Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "cons-pos-alistp")
(include-book "string-string-alistp")
(include-book "string-symbollist-alistp")
(include-book "symbol-nat-alistp")
(include-book "symbol-pos-alistp")
(include-book "symbol-pseudoterm-alistp")
(include-book "symbol-string-alistp")
(include-book "symbol-symbol-alistp")
(include-book "symbol-truelist-alistp")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/typed-alists
  :parents (std)
  :short "Typed alists."
  :long
  (xdoc::topstring
   (xdoc::p
    "A library of alists with keys and values of specific types.
     These are built-in types, or ``general'' types in Std.")))
