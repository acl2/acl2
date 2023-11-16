; Use with-supporters to just get the code of the Proof Advice tool
;
; Copyright (C) 2022-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/io/read-string-light" :dir :system) ; avoids error below
(include-book "kestrel/htclient/post-light" :dir :system) ; avoids error below
(include-book "tools/with-supporters" :dir :system)

(with-supporters
 (local (include-book "advice"))
 :names (acl2::make-event-quiet
         help::advice-fn
         help::advice
         advice ; synonym in ACL2 package
         help::thm-advice-fn
         help::thm-advice
         thm-advice ; synonym in ACL2 package
         help::defthm-advice-fn
         help::defthm-advice
         defthm-advice ; synonym in ACL2 package
         help::all-successful-actions-for-checkpoints ; for Matt's tool
         )
 :tables (help::advice-options))
