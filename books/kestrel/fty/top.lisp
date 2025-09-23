; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "any-nat-map")
(include-book "bag")
(include-book "bin-digit-char-list")
(include-book "bit-list")
(include-book "byte")
(include-book "byte-list")
(include-book "byte-list20")
(include-book "byte-list32")
(include-book "byte-list64")
(include-book "character-list")
(include-book "character-list-result")
(include-book "character-result")
(include-book "character-set")
(include-book "character-any-map")
(include-book "database")
(include-book "dec-digit-char-list")
(include-book "defbyte")
(include-book "defbyte-ihs-theorems")
(include-book "defbyte-standard-instances")
(include-book "defbyte-standard-instances-ihs-theorems")
(include-book "defbytelist")
(include-book "defbytelist-standard-instances")
(include-book "deffixequiv-sk")
(include-book "deffixequiv-sk-doc")
(include-book "deffixtype-alias")
(include-book "defflatsum")
(include-book "defflatsum-doc")
(include-book "deffold-map")
(include-book "deffold-map-doc")
(include-book "deffold-reduce")
(include-book "deffold-reduce-doc")
(include-book "deflist-of-len")
(include-book "defmake-self")
(include-book "defmake-self-doc")
(include-book "fty-omap")
;(include-book "defomap")
(include-book "fty-set")
;(include-book "defset")
(include-book "defresult")
(include-book "defsubtype")
(include-book "defunit")
(include-book "defunit-doc")
(include-book "dependencies")
(include-book "fold")
(include-book "hex-digit-char-list")
(include-book "integer-result")
(include-book "map")
(include-book "maybe-string")
(include-book "maybe-string-result")
(include-book "nat-list-result")
(include-book "nat-natlist")
(include-book "nat-natlist-result")
(include-book "nat-option")
(include-book "nat-option-list")
(include-book "nat-option-result")
(include-book "nat-option-list-result")
(include-book "natoption-natoptionlist")
(include-book "natoption-natoptionlist-result")
(include-book "nat-result")
(include-book "nat-set")
(include-book "nati")
(include-book "nibble")
(include-book "nibble-list")
(include-book "oct-digit-char-list")
(include-book "pos-list")
(include-book "pos-option")
(include-book "pos-set")
(include-book "pseudo-event-form")
(include-book "pseudo-event-form-list")
(include-book "set")
(include-book "string-set")
(include-book "string-list-result")
(include-book "string-result")
(include-book "strings-decimal-fty")
(include-book "symbol-set")
(include-book "dec-digit-char")
(include-book "hex-digit-char")
(include-book "oct-digit-char")
(include-book "bin-digit-char")
(include-book "string-stringlist-alist")
(include-book "symbol-pseudoeventform-alist")
(include-book "symbol-pseudoterm-alist")
(include-book "string-option")
(include-book "ubyte32-option")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc fty-extensions
  :parents (acl2::kestrel-books fty)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seetopic "fty" "FTY")
                   " in the "
                   (xdoc::seetopic "acl2::kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring-p
   "These could be merged with FTY at some point."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc specific-types
  :parents (fty-extensions fty)
  :short
  (xdoc::topstring "Various specific "
                   (xdoc::seetopic "fty" "fixtypes")
                   ".")
  :long
  (xdoc::topstring-p
   "These complement the "
   (xdoc::seetopic "basetypes" "base types")
   " and the "
   (xdoc::seetopic "baselists" "base list types")
   "."))
