; FTY Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(local (include-book "centaur/fty/top" :dir :system))
(local (include-book "std/basic/two-nats-measure" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "defmake-self"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-make-self (fn arg)
  `(acl2::assert-equal (,fn ,arg) ',arg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  ;; This example algebraic type clique is taken from deffold-reduce-tests.lisp
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

  ;; Test on type clique name
  (acl2::must-succeed*
    (defmake-self exprs)

    (test-make-self
      aexpr-make-self
      (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                  (aexpr-var "foo")
                  (aexpr-var "bar")))

    :with-output-off nil)

  ;; Test on type name
  (acl2::must-succeed*
    (defmake-self bexpr)

    (test-make-self
      aexpr-make-self
      (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                  (aexpr-var "foo")
                  (aexpr-var "bar")))
    :with-output-off nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test different layouts

(acl2::must-succeed*
  (deftypes exprs
    (deftagsum aexpr
      (:const ((value acl2::int)))
      (:var ((name string)))
      (:add ((left aexpr) (right aexpr)))
      (:cond ((test bexpr) (left aexpr) (right aexpr)))
      :layout :alist
      :pred aexprp)
    (deftagsum bexpr
      (:true ())
      (:false ())
      (:and ((left bexpr) (right bexpr)))
      (:less ((left aexpr) (right aexpr)))
      :layout :tree
      :pred bexprp))

  (defmake-self exprs)

  (test-make-self
    aexpr-make-self
    (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                (aexpr-var "foo")
                (aexpr-var "bar")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test with type dependencies outside the clique

(acl2::must-succeed*
  (defprod ident
    ((name string))
    :pred identp)

  (deftypes exprs
    (deftagsum aexpr
      (:const ((value acl2::int)))
      (:var ((name ident)))
      (:add ((left aexpr) (right aexpr)))
      (:cond ((test bexpr) (left aexpr) (right aexpr)))
      :pred aexprp)
    (deftagsum bexpr
      (:true ())
      (:false ())
      (:and ((left bexpr) (right bexpr)))
      (:less ((left aexpr) (right aexpr)))
      :pred bexprp))

  (acl2::must-succeed*
    (defmake-self ident)
    (defmake-self exprs)

    (test-make-self
      aexpr-make-self
      (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                  (aexpr-var (ident "foo"))
                  (aexpr-var (ident "bar"))))

    :with-output-off nil)

  (acl2::must-succeed*
    (defmake-self exprs)

    (test-make-self
      aexpr-make-self
      (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                  (aexpr-var (ident "foo"))
                  (aexpr-var (ident "bar"))))
    :with-output-off nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test non-clique

(acl2::must-succeed*
  (deftagsum aexpr
    (:const ((value acl2::int)))
    (:var ((name string)))
    (:add ((left aexpr) (right aexpr)))
    :pred aexprp)

  (defmake-self aexpr)

  (test-make-self
    aexpr-make-self
    (aexpr-add (aexpr-var "foo") (aexpr-var "bar")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test redundant calls

(acl2::must-succeed*
  (deftagsum aexpr
    (:const ((value acl2::int)))
    (:var ((name string)))
    (:add ((left aexpr) (right aexpr)))
    :pred aexprp)

  (defmake-self aexpr)
  (defmake-self aexpr)
  (defmake-self aexpr)

  (test-make-self
    aexpr-make-self
    (aexpr-add (aexpr-var "foo") (aexpr-var "bar")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test lists

(acl2::must-succeed*
  (deflist my-nat-list
    :elt-type acl2::nat
    :true-listp t
    :pred my-nat-listp)

  (defmake-self my-nat-list)

  (test-make-self
    my-nat-list-make-self
    (list 1 2 3))

  (test-make-self
    my-nat-list-make-self
    nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test omaps

(acl2::must-succeed*
  (defomap nat-map
    :key-type acl2::nat
    :val-type acl2::nat
    :pred nat-mapp)

  (defmake-self nat-map)

  (test-make-self
    nat-map-make-self
    (omap::update 1 10
                  (omap::update 2 20 nil)))

  :with-output-off nil)
