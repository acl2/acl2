; Use with-supporters to just get the code of the Proof Advice tool
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/io/read-string-light" :dir :system) ; avoids error below
(include-book "kestrel/htclient/post" :dir :system) ; avoids error below
(include-book "tools/with-supporters" :dir :system)
(set-state-ok t) ; avoids error below

(with-supporters
 (local (include-book "advice"))
 :names (acl2::make-event-quiet
         help::advice-fn
         help::advice
         advice ; synonym in ACL2 package
         ))
