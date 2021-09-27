; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defresult")
(include-book "nat-natlist")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult nat/natlist-result
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of errors and
          natural numbers and lists or natural numbers."
  :ok nat/natlist
  :pred nat/natlist-resultp
  :prepwork ((local (in-theory (e/d (nat/natlist-kind) (nat/natlist-p))))))
