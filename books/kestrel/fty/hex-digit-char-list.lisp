; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "hex-digit-char")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/hex-digit-char-listp" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist hex-digit-char-list
  :parents (fty::fty-extensions fty::specific-types pos-listp)
  :short "Fixtype of lists of hexadecimal digit characters."
  :elt-type hex-digit-char
  :true-listp t
  :elementp-of-nil nil
  :pred hex-digit-char-listp
  :prepwork ((local (in-theory (enable nfix)))))
