; String Utilities -- Kinds of Strings
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/defs" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-kinds
  :parents (string-utilities)
  :short "Predicates that characterize various kinds of strings.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nonempty-stringp (x)
  :returns (yes/no booleanp)
  :parents (string-kinds)
  :short "Recognize non-empty strings."
  (not (equal (str-fix x) ""))
  ///

  (defrule stringp-when-nonempty-stringp
    (implies (nonempty-stringp x)
             (stringp x))))

(std::deflist nonempty-string-listp (x)
  (nonempty-stringp x)
  :parents (string-kinds nonempty-stringp)
  :short "Recognize true lists of nonempty strings."
  :true-listp t
  :elementp-of-nil nil)
