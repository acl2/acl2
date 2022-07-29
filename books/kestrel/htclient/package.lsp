; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "HTCLIENT"
  (append std::*std-exports*
          set::*sets-exports*
          '(str::cat
            str::natstr
            include-raw
            b*
            assert!
            progn$
            defxdoc
            defconsts
            definline
            definlined
            defsection
            defsection-progn
            live-state-p
            value
            msg)
          acl2::*standard-acl2-imports*))
