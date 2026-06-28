; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "hex-digit-char-list")
(include-book "defresult")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult hex-digit-char-list-result
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of errors and lists of hexadecimal digit characters."
  :ok hex-digit-char-list
  :pred hex-digit-char-list-resultp)
