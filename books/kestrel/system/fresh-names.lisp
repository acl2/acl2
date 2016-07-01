; Fresh Names
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides utilities for generating fresh names,
; i.e. names that do not already occur in the world, in terms, etc.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fresh-names
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities for generating fresh names.")

(define fresh-name-in-world-with-$s ((name symbolp)
                                     (names-to-avoid symbol-listp)
                                     (w plist-worldp))
  :returns (fresh-name symbolp)
  :prepwork ((program))
  :parents (fresh-names)
  :short
  "Append as many @('$') signs to @('name')
  as needed to make the name new in the world, i.e. not already in use,
  and not among the given names to avoid."
  :long
  "<p>
  If @('name') is already new and not among the names to avoid,
  it is left unchanged.
  </p>"
  (if (or (logical-namep name w)
          (member name names-to-avoid))
      (fresh-name-in-world-with-$s (packn (list name '$)) names-to-avoid w)
    name))
