; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(local (include-book "deffold-map"))

(local (include-book "centaur/fty/top" :dir :system))
(local (include-book "std/basic/two-nats-measure" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

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

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map invert
    :types (exprs)
    :override
    ((bexpr :true (bexpr-false))
     (bexpr :false (bexpr-true)))
    :name test)

  (acl2::assert-equal
    (aexpr-invert (aexpr-cond (bexpr-false) (aexpr-const 0) (aexpr-const 1)))
    (aexpr-cond (bexpr-true) (aexpr-const 0) (aexpr-const 1)))

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map simpadd0
    :types (exprs)
    :override
    ((aexpr
      :add
      (b* ((left (aexpr-simpadd0 aexpr.left))
           (right (aexpr-simpadd0 aexpr.right)))
        (cond ((equal left (aexpr-const 0))
               right)
              ((equal right (aexpr-const 0))
               left)
              (t (aexpr-add left right))))))
    :name test)

  (acl2::assert-equal
    (aexpr-simpadd0 (aexpr-add (aexpr-const 42)
                               (aexpr-add (aexpr-const 0) (aexpr-const 0))))
    (aexpr-const 42))

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map subst-vars
    :types (exprs)
    :extra-args ((alist alistp))
    :override
    ((aexpr
      :var
      (let ((lookup (assoc-equal aexpr.name alist)))
        (if (and lookup
                 (stringp (cdr lookup)))
            (aexpr-var (cdr lookup))
          (aexpr-fix aexpr)))))
    :name test)

  (acl2::assert-equal
    (bexpr-subst-vars (bexpr-less (aexpr-var "x") (aexpr-var "y"))
                      (acons "x" "foo" nil))
    (bexpr-less (aexpr-var "foo") (aexpr-var "y")))

  ;;;;;;;;;;;;;;;;;;;;

  :with-output-off nil)

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

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map becomes-bar
    :types (foo+)
    :override
    ((foo :list (foo-bar))
     (foo :omap (foo-bar)))
    :name test)

  (acl2::assert-equal
    (foo-omap-becomes-bar
      (omap::update 0
                    (foo-list nil)
                    (omap::update 1
                                  (foo-omap nil)
                                  nil)))
    (omap::update 0
                  (foo-bar)
                  (omap::update 1
                                (foo-bar)
                                nil)))

  ;;;;;;;;;;;;;;;;;;;;

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (deftypes foo+
    (deftagsum foo
      (:list ((list foo-list)))
      (:omap ((omap foo-omap)))
      (:int ((int acl2::int)))
      :pred foop)
    ;; This time without :true-listp t
    (deflist foo-list
      :elt-type foo
      :pred foo-listp)
    (defomap foo-omap
      :key-type acl2::int
      :val-type foo
      :pred foo-omapp))

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map replace-int
    :types (foo+)
    :extra-args ((i integerp))
    :override
    ((foo :int (foo-int i)))
    :name test)

  (acl2::assert-equal
    (foo-omap-replace-int
      (omap::update 0
                    (foo-list nil)
                    (omap::update 1
                                  (foo-int 2)
                                  nil))
      42)
    (omap::update 0
                  (foo-list nil)
                  (omap::update 1
                                (foo-int 42)
                                nil)))

  ;;;;;;;;;;;;;;;;;;;;

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (deftypes foo+
    (deftagsum foo
      (:bar ((foo? foo-optionp)))
      (:baz ())
      :measure (acl2::nat-list-measure (list (acl2-count x) 0))
      :pred foop)
    (defoption foo-option
      foo
      :measure (acl2::nat-list-measure (list (acl2-count x) 1))
      :pred foo-optionp))

  ;;;;;;;;;;;;;;;;;;;;

  (deffold-map becomes-baz
    :types (foo+)
    :override
    ((foo :bar (foo-baz)))
    :name test)

  (acl2::assert-equal
    (foo-option-becomes-baz (foo-bar nil))
    (foo-baz))

  ;;;;;;;;;;;;;;;;;;;;

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extra arguments must be made ignorable in the generated functions:
; an :OVERRIDE term need not mention every extra argument
; (nor the main formal),
; so without the `ignorable' declaration the unused extra formal
; would cause an error.

; Product type whose override term does not mention the extra argument.

(acl2::must-succeed*
  (defprod ipair
    ((left acl2::int) (right acl2::int))
    :pred ipairp)

  (deffold-map norm
    :types (ipair)
    :extra-args ((extra booleanp))
    :override ((ipair (ipair 0 0)))
    :name test)

  (acl2::assert-equal (ipair-norm (ipair 1 2) t) (ipair 0 0))
  (acl2::assert-equal (ipair-norm (ipair 3 4) nil) (ipair 0 0))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sum type whose override term does not mention the extra argument.

(acl2::must-succeed*
  (deftagsum rgb
    (:red ())
    (:green ())
    (:blue ())
    :pred rgbp)

  (deffold-map norm
    :types (rgb)
    :extra-args ((extra booleanp))
    :override ((rgb (rgb-red)))
    :name test)

  (acl2::assert-equal (rgb-norm (rgb-blue) t) (rgb-red))
  (acl2::assert-equal (rgb-norm (rgb-green) nil) (rgb-red))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List type whose override term mentions neither the main formal
; nor the extra argument, here a standalone (singly recursive) list.

(acl2::must-succeed*
  (deflist intlist
    :elt-type acl2::int
    :true-listp t
    :pred intlistp)

  (deffold-map clear
    :types (intlist)
    :extra-args ((extra booleanp))
    :override ((intlist nil))
    :name test)

  (acl2::assert-equal (intlist-clear '(1 2 3) t) nil)
  (acl2::assert-equal (intlist-clear nil nil) nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; List type override that mentions neither the main formal
; nor the extra argument, here in a mutually recursive clique.

(acl2::must-succeed*
  (deftypes tree+
    (deftagsum tree
      (:leaf ((val acl2::int)))
      (:node ((children treelist)))
      :pred treep)
    (deflist treelist
      :elt-type tree
      :true-listp t
      :pred treelistp))

  (deffold-map clear
    :types (tree+)
    :extra-args ((extra booleanp))
    :override ((treelist nil))
    :name test)

  (acl2::assert-equal
    (treelist-clear (list (tree-leaf 1) (tree-leaf 2)) t)
    nil)
  (acl2::assert-equal
    (tree-clear (tree-node (list (tree-leaf 1))) nil)
    (tree-node nil))

  :with-output-off nil)
