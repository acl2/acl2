; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "deffold-reduce")

(include-book "centaur/fty/top" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftypes exprs
  (deftagsum aexpr
    (:const ((value acl2::int)))
    (:var ((name string)))
    (:add ((left aexpr) (right aexpr)))
    (:cond ((test bexpr) (left aexpr) (right aexpr)))
    :pred aexprp)
  (deftagsum bexpr
    (:true ())
    (:false ())
    (:and ((left bexpr) (right bexpr)))
    (:less ((left aexpr) (right aexpr)))
    :pred bexprp))

(deffold-reduce vars
  :types (exprs)
  :result string-listp
  :default nil
  :combine append
  :override ((aexpr :var (list (aexpr-var->name aexpr)))))
