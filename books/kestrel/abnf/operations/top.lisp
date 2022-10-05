; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "well-formedness")
(include-book "closure")
(include-book "in-terminal-set")
(include-book "ambiguity")
(include-book "plugging")
(include-book "renaming")
(include-book "removal")
(include-book "rule-utilities")

(include-book "../semantics")

(include-book "kestrel/std/strings/letter-chars" :dir :system)
(include-book "kestrel/std/strings/letter-digit-dash-chars" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "kestrel/utilities/osets" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)
(include-book "kestrel/fty/string-list-result" :dir :system)

(local (include-book "kestrel/utilities/lists/len-const-theorems" :dir :system))
(local (include-book "kestrel/utilities/oset-theorems" :dir :system))
(local (include-book "kestrel/utilities/typed-lists/nat-list-fix-theorems" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations
  :parents (abnf)
  :short "Operations on ABNF grammars."
  :order-subtopics t)
