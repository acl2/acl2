; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "guard-verified-p")
(include-book "theorem-symbolp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-verified-p+ ((fn/thm symbolp) (wrld plist-worldp))
  :returns (yes/no booleanp)
  :parents (std/system/function-queries std/system/theorem-queries)
  :short "Enhanced variant of @(tsee guard-verified-p)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee guard-verified-p),
    but it causes an error if called on a symbol
    that does not name a function or theorem.")
  (if (and (not (function-symbolp fn/thm wrld))
           (not (theorem-symbolp fn/thm wrld)))
      (raise "The symbol ~x0 does not name a function or theorem." fn/thm)
    (guard-verified-p fn/thm wrld))
  ///

  (defthmd function/theorem-symbolp-when-guard-verified-p+
    (implies (guard-verified-p+ fn/thm wrld)
             (or (function-symbolp fn/thm wrld)
                 (theorem-symbolp fn/thm wrld)))))
