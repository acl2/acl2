; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "deffold-reduce")
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "centaur/fty/top" :dir :system)

(local (include-book "std/typed-lists/string-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
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
    :override ((aexpr :var (list (aexpr-var->name aexpr))))
    :name test))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (deftypes foo+
    (deftagsum foo
      (:list ((list foo-list)))
      (:omap ((omap foo-omap)))
      (:bar ())
      :pred foop)
    (deflist foo-list
      :elt-type foo
      :true-listp t
      :pred foo-listp)
    (defomap foo-omap
      :key-type acl2::int
      :val-type foo
      :pred foo-omapp))

  (deffold-reduce count-bars
    :types (foo+)
    :result natp
    :default 0
    :combine binary-+
    :override
    ((foo :bar 1))
    :name test))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (deftypes foo+
    (deftagsum foo
      (:list ((list foo-list)))
      (:omap ((omap foo-omap)))
      (:bar ())
      :pred foop)
    ;; This time without :true-listp t
    (deflist foo-list
      :elt-type foo
      :pred foo-listp)
    (defomap foo-omap
      :key-type acl2::int
      :val-type foo
      :pred foo-omapp))

  (deffold-reduce count-bars
    :types (foo+)
    :result natp
    :default 0
    :combine binary-+
    :override
    ((foo :bar 1))
    :name test))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Overriding the function on a list type, here in a mutually recursive clique.
; The accompanying list theorems are omitted when the list is overridden,
; so the overriding term need not satisfy them:
; here it returns a nonzero constant even on the empty list,
; which would violate the otherwise generated <type>-<suffix>-when-atom theorem.

(acl2::must-succeed*
  (deftypes foo+
    (deftagsum foo
      (:list ((list foo-list)))
      (:omap ((omap foo-omap)))
      (:bar ())
      :pred foop)
    (deflist foo-list
      :elt-type foo
      :true-listp t
      :pred foo-listp)
    (defomap foo-omap
      :key-type acl2::int
      :val-type foo
      :pred foo-omapp))

  (deffold-reduce count-bars
    :types (foo+)
    :result natp
    :default 0
    :combine binary-+
    :override
    ((foo :bar 1)
     (foo-list 5))
    :name test)

  ;; The overriding term is used as the body of the list function.
  (assert-event (equal (foo-list-count-bars nil) 5))
  (assert-event (equal (foo-list-count-bars (list (foo-bar) (foo-bar))) 5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Overriding the function on a standalone (singly recursive) list type.

(acl2::must-succeed*
  (deflist intlist
    :elt-type acl2::int
    :true-listp t
    :pred intlistp)

  (deffold-reduce sz
    :types (intlist)
    :result natp
    :default 0
    :combine binary-+
    :override
    ((intlist 7))
    :name test)

  (assert-event (equal (intlist-sz nil) 7))
  (assert-event (equal (intlist-sz '(1 2 3)) 7)))
