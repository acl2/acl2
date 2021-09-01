; ACL2 customization file for jvm/ directory
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; load the user's acl2-customization.lsp, if any:
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(include-book "kestrel/jvm/portcullis" :dir :system)

(reset-prehistory)

;; todo: perhaps switch to JVM package but some books in this dir are in the ACL2 package
