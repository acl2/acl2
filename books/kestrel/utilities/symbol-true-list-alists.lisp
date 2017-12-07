; Alists from Symbols to NIL-Terminated Lists
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defalist" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist symbol-true-list-alistp (x)
  :key (symbolp x)
  :val (true-listp x)
  :parents (kestrel-utilities alists)
  :short "Recognize @('nil')-terminated alists
          from symbols to @('nil')-terminated lists."
  :keyp-of-nil t
  :valp-of-nil t
  :true-listp t)
