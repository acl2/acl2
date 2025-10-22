; FTY Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "dec-digit-char")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/dec-digit-char-listp" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist dec-digit-char-list
  :parents (fty::fty-extensions fty::specific-types dec-digit-char)
  :short "Fixtype of lists of decimal digit characters."
  :elt-type dec-digit-char
  :true-listp t
  :elementp-of-nil nil
  :pred dec-digit-char-listp
  :prepwork ((local (in-theory (enable nfix)))))
