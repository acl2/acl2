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
     (bexpr :false (bexpr-true))))

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
              (t (aexpr-add left right)))))))

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
          (aexpr-fix aexpr))))))

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
     (foo :omap (foo-bar))))

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
    ((foo :int (foo-int i))))

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
    ((foo :bar (foo-baz))))

  (acl2::assert-equal
    (foo-option-becomes-baz (foo-bar nil))
    (foo-baz))

  ;;;;;;;;;;;;;;;;;;;;

  :with-output-off nil)
