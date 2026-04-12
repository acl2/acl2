; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "REMORA" (append
                  (set-difference-eq *std-pkg-symbols*
                                     '(atom
                                       atom-listp
                                       check-type
                                       function
                                       functionp
                                       sort
                                       termp
                                       type
                                       typep))
                  '(bool
                    defmacro+
                    defxdoc+
                    int
                    lnfix
                    nat
                    nat-list
                    nat-list-fix
                    fty::patbind-ok
                    fty::reserr
                    fty::reserrp
                    str::string-list)))
