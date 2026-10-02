; Futhark Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "FUTHARK"
  (append
   (set-difference-eq *std-pkg-symbols*
                      '(type typep))
   '(fty::deflist
     fty::defoption
     fty::defprod
     fty::defresult
     fty::deftagsum
     fty::deftypes
     fty::ok
     fty::okf
     fty::patbind-ok
     fty::patbind-okf
     fty::reserr
     fty::reserrf
     fty::reserrf-push
     fty::reserrp
     defxdoc+
     defmacro+
     nat-list-fix
     std::defret-mutual
     str::string-list-fix
     str-fix)))
