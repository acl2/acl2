; Use with-supporters to just get the code of the x86 Axe Rewriter
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/with-supporters" :dir :system)

(include-book "centaur/misc/tshell" :dir :system) ; needs to be non-local since it has Raw Lisp code

(defttag :rewriter-x86-code-only)

;; todo: also need to include all the calls of add-known-boolean (making sure
;; the functions are defined).  Or use the :tables option to get the
;; :known-booleans-table.

(with-supporters
 (local (include-book "rewriter-x86"))
 :names (simplify-terms-to-terms-x86
          simplify-dag-x86
          ;; make-rule-alist!
          ))
