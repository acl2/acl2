; Use with-supporters to just get the code of the Axe Basic Rewriter
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

;; todo: also need to include all the calls of add-known-boolean (making sure
;; the functions are defined)

(with-supporters
 (local (include-book "rewriter-basic"))
 :names (simp-term-basic
         make-rule-alist!))
