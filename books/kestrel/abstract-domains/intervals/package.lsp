; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "INTERVAL"
  (append '(define-sk
            defxdoc
            defxdoc+
            maybe-rational-equiv
            maybe-rational-fix
            maybe-rationalp
            number-equiv
            rational-equiv
            rational-fix
            )
          (set-difference-eq
            *std-pkg-symbols*
            #!STD'(*
                   +
                   -
                   associativity-of-+
                   binary-*
                   binary-+
                   commutativity-of-+
                   emptyp
                   fix
                   get
                   intersect
                   max
                   min
                   ))))
