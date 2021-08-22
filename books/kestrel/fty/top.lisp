; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "bag")
(include-book "bit-list")
(include-book "byte")
(include-book "byte-list")
(include-book "byte-list20")
(include-book "byte-list32")
(include-book "byte-list64")
(include-book "character-result")
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
(include-book "deflist-of-len")
(include-book "fty-omap")
;(include-book "defomap")
(include-book "fty-set")
;(include-book "defset")
(include-book "defresult")
(include-book "defsubtype")
(include-book "defunit")
(include-book "defunit-doc")
(include-book "map")
(include-book "nat-list-result")
(include-book "nat-result")
(include-book "nat-set")
(include-book "nati")
(include-book "nibble")
(include-book "nibble-list")
(include-book "set")
(include-book "dec-digit-char")
(include-book "hex-digit-char")
(include-book "oct-digit-char")
(include-book "bin-digit-char")

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
