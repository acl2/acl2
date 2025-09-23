; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/baselists" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (:e tau-system))))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap string-stringlist-map
  :key-type string
  :val-type str::string-list
  :pred string-stringlist-mapp)

(in-theory (disable string-listp-of-cdr-of-assoc-string-stringlist-mapp))

;; Stronger version of string-listp-of-cdr-of-assoc-string-stringlist-mapp
(defruled string-listp-of-cdr-of-assoc-when-string-stringlist-map
  (implies (string-stringlist-mapp map)
           (string-listp (cdr (omap::assoc key map))))
  :induct t
  :enable (string-stringlist-mapp
           omap::assoc))
