; FTY Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)
; Contributions by: Eric McCarthy (bendyarm at GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test :ctor-style :maker
;; The maker style emits keyword constructor macros (make-<type> :field ...)
;; instead of by-position constructor calls.

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

  (defmake-self exprs :ctor-style :maker)

  ;; a single product
  (acl2::assert-equal
    (aexpr-make-self (aexpr-var "foo"))
    '(make-aexpr-var :name "foo"))

  ;; nested products, with field keywords in field order
  (acl2::assert-equal
    (aexpr-make-self (aexpr-add (aexpr-const 1) (aexpr-var "x")))
    '(make-aexpr-add :left (make-aexpr-const :value 1)
                     :right (make-aexpr-var :name "x")))

  ;; deeper, crossing into the other type and reaching field-less products
  (acl2::assert-equal
    (aexpr-make-self (aexpr-cond (bexpr-and (bexpr-true) (bexpr-false))
                                 (aexpr-var "foo")
                                 (aexpr-var "bar")))
    '(make-aexpr-cond :test (make-bexpr-and :left (make-bexpr-true)
                                            :right (make-bexpr-false))
                      :left (make-aexpr-var :name "foo")
                      :right (make-aexpr-var :name "bar")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test :ctor-style :positional (the explicit default)
;; The output is the by-position constructor form, so it matches the source
;; constructor call (the property test-make-self checks).

(acl2::must-succeed*
  (deftagsum aexpr
    (:const ((value acl2::int)))
    (:var ((name string)))
    (:add ((left aexpr) (right aexpr)))
    :pred aexprp)

  (defmake-self aexpr :ctor-style :positional)

  (test-make-self
    aexpr-make-self
    (aexpr-add (aexpr-var "foo") (aexpr-const 3)))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test that an invalid :ctor-style is rejected

(acl2::must-succeed*
  (deftagsum aexpr
    (:const ((value acl2::int)))
    (:var ((name string)))
    :pred aexprp)

  (acl2::must-fail (defmake-self aexpr :ctor-style :bogus))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test that :ctor-style :maker is rejected when a type omits its keyword
;; constructor macro (:no-ctor-macros), since :maker would emit a call to a
;; macro that does not exist.  :positional, which uses the by-position
;; constructor, still works.

(acl2::must-succeed*
  (defprod noctor ((f1 acl2::int) (f2 string))
    :pred noctorp
    :no-ctor-macros t)

  (acl2::must-fail (defmake-self noctor :ctor-style :maker))

  (defmake-self noctor :ctor-style :positional)
  (test-make-self noctor-make-self (noctor 5 "hi"))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The :maker check also fires when the :no-ctor-macros type is reached only as
;; a dependency of the requested type.

(acl2::must-succeed*
  (defprod noctor ((g acl2::int))
    :pred noctorp
    :no-ctor-macros t)
  (defprod outer ((inner noctor) (tag string))
    :pred outerp)

  (acl2::must-fail (defmake-self outer :ctor-style :maker))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test the :universal dispatcher.
;; One generated function dispatches on any AST node, a homogeneous list of
;; nodes, or the empty list, and returns a reserrp for anything else.  Here
;; the node types have disjoint tags, so every value is unambiguous; the
;; dispatcher uses the default :positional style, so its output matches the
;; source constructor form.

(acl2::must-succeed*
  (deftypes my-ast
    (deftagsum node
      (:leaf ((val acl2::int)))
      (:branch ((children node-list)))
      :pred nodep)
    (deflist node-list
      :elt-type node
      :true-listp t
      :pred node-listp))

  (defmake-self my-ast :universal node-self)

  ;; a single node, dispatched by its recognizer
  (test-make-self node-self (node-leaf 5))
  (test-make-self node-self
                  (node-branch (list (node-leaf 1) (node-leaf 2))))

  ;; a homogeneous list of nodes becomes a (list ...) form
  (test-make-self node-self
                  (list (node-leaf 1) (node-leaf 2) (node-leaf 3)))

  ;; the empty list is nil
  (acl2::assert-equal (node-self nil) nil)

  ;; a value that is neither a node nor a node list is a reserrp
  (acl2::assert-event (reserrp (node-self 42)))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test the :universal dispatcher on ambiguous and heterogeneous values.
;; PA and PB are distinct types with overlapping recognizers (same :list
;; layout and field types), so a value of one is also recognized as the other.

(acl2::must-succeed*
  (defprod pa ((fa acl2::int) (fb acl2::int)) :pred pap :layout :list)
  (defprod pb ((fa acl2::int) (fb acl2::int)) :pred pbp :layout :list)
  (deftagsum wrap
    (:a ((p pa)))
    (:b ((q pb)))
    :pred wrapp)

  (defmake-self wrap :universal wrap-self)

  ;; a value matching more than one node type is ambiguous: reserrp
  (acl2::assert-event (reserrp (wrap-self (pa 5 6))))

  ;; wrapping disambiguates (only WRAP recognizes a tagged value)
  (test-make-self wrap-self (wrap-a (pa 5 6)))

  ;; a list whose elements have no single common type is heterogeneous: reserrp
  (acl2::assert-event
    (reserrp (wrap-self (list (wrap-a (pa 1 2)) (pa 3 4)))))

  ;; a list whose elements are each ambiguous has no single common type: reserrp
  (acl2::assert-event
    (reserrp (wrap-self (list (pa 1 2) (pa 3 4)))))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test redundant re-submission of a :universal call (same name, same clique):
;; it is a no-op and the dispatcher keeps working.

(acl2::must-succeed*
  (deftypes my-ast
    (deftagsum node
      (:leaf ((val acl2::int)))
      (:branch ((children node-list)))
      :pred nodep)
    (deflist node-list
      :elt-type node
      :true-listp t
      :pred node-listp))

  (defmake-self my-ast :universal node-self)
  (defmake-self my-ast :universal node-self)
  (defmake-self my-ast :universal node-self)

  (test-make-self node-self (node-leaf 7))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test that reusing a :universal name for a different clique is rejected.

(acl2::must-succeed*
  (deftagsum t1 (:c1 ((v acl2::int))) :pred t1p)
  (deftagsum t2 (:c2 ((v acl2::int))) :pred t2p)

  (defmake-self t1 :universal both-self)
  (acl2::must-fail (defmake-self t2 :universal both-self))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test that a :universal name whose derived helper name is already in use is
;; rejected up front (the helper names are derived from the :universal name).

(acl2::must-succeed*
  (deftagsum node
    (:leaf ((val acl2::int)))
    :pred nodep)

  (defun foo-node-cands (x) x)
  (acl2::must-fail (defmake-self node :universal foo))

  :with-output-off nil)
