; Theorems about True Lists of True Lists
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-true-list-lists

  :parents (theorems-about-non-kestrel-books true-list-listp std/typed-lists)

  :short "Theorems about true lists of true lists."

  :long
  "<p>
   These are generated via @(tsee std::deflist).
   </p>"

  (std::deflist true-list-listp (x)
    (true-listp x)
    :true-listp t
    :elementp-of-nil t
    :parents nil))
