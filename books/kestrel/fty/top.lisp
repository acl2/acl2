; FTY -- Kestrel Extensions
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "defbyte")
(include-book "defbyte-instances")
(include-book "defbytelist")
(include-book "defbytelist-instances")
(include-book "deffixtype-alias")
(include-book "deflist-of-len")
(include-book "defomap")
(include-book "defset")
(include-book "map")
(include-book "nati")
(include-book "set")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc fty-extensions
  :parents (acl2::kestrel-books fty)
  :short
  (xdoc::topstring "Extensions of "
                   (xdoc::seeurl "fty" "FTY")
                   " in the "
                   (xdoc::seeurl "acl2::kestrel-books" "Kestrel Books")
                   ".")
  :long
  (xdoc::topstring-p
   "These could be merged with FTY at some point."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc specific-types
  :parents (fty-extensions fty)
  :short
  (xdoc::topstring "Various specific "
                   (xdoc::seeurl "fty" "fixtypes")
                   ".")
  :long
  (xdoc::topstring-p
   "These complement the "
   (xdoc::seeurl "basetypes" "base types")
   " and the "
   (xdoc::seeurl "baselists" "base list types")
   "."))
