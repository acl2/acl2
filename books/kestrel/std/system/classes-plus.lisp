; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "classes")
(include-book "theorem-symbolp")

(include-book "std/typed-alists/keyword-to-keyword-value-list-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classes+ ((thm symbolp) (wrld plist-worldp))
  :returns (classes keyword-to-keyword-value-list-alistp)
  :parents (std/system/theorem-queries)
  :short "Enhanced variant of @(tsee classes)."
  :long
  (xdoc::topstring-p
   "This returns the same result as @(tsee classes),
    but it includes a run-time check (which should always succeed) on the result
    that allows us to prove the return type theorem
    without strengthening the guard on @('wrld').
    Furthermore, this utility causes an error if called on
    a symbol that does not name a theorem.")
  (if (not (theorem-symbolp thm wrld))
      (raise "The symbol ~x0 does not name a theorem." thm)
    (b* ((result (classes thm wrld)))
      (if (keyword-to-keyword-value-list-alistp result)
          result
        (raise "Internal error: ~
                the rule classes ~x0 of ~x1 are not an alist
                from keywords to keyword-value lists."
               result thm)))))
