; AIR Library Model M0 -- Package
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)  ; for STR stuff

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "AIR-M0"
  (append '(;; added symbols
            bit->bool
            bit-listp
            bool-fix
            bool->bit
            define-sk
            defund-sk
            defxdoc+
            defmacro+
            nat-list-fix
            ;; ubyte8 fixtype symbols from kestrel/fty/ubyte8
            ubyte8
            ubyte8p
            ubyte8-fix
            ubyte8-equiv
            ;; ubyte8-list fixtype symbols from kestrel/fty/ubyte8-list
            ubyte8-listp
            )
          (set-difference-eq
           *std-pkg-symbols*
           '(;; removed symbols
             program
             trace
             ))))
