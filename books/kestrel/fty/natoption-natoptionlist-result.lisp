; FTY Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "natoption-natoptionlist")
(include-book "defresult")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult natoption/natoptionlist-result
  :parents (fty::fty-extensions fty::specific-types)
  :short "Fixtype of errors and
          optional natural numbers and lists of optional natural numbers."
  :ok natoption/natoptionlist
  :pred natoption/natoptionlist-resultp
  :prepwork ((local (in-theory (e/d (natoption/natoptionlist-kind)
                                    (natoption/natoptionlist-p))))))
