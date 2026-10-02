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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Extra arguments must be made ignorable in the generated functions:
; an :OVERRIDE term (or a combination that reduces to the default)
; need not mention every extra argument,
; so without the `ignorable' declaration the unused extra formal
; would cause an error.

; Product type whose override term does not mention the extra argument.

(acl2::must-succeed*
  (defprod ipair
    ((left acl2::int) (right acl2::int))
    :pred ipairp)

  (deffold-reduce sz
    :types (ipair)
    :extra-args ((extra booleanp))
    :result natp
    :default 0
    :combine binary-+
    :override ((ipair 3))
    :name test)

  (assert-event (equal (ipair-sz (ipair 1 2) nil) 3))
  (assert-event (equal (ipair-sz (ipair 1 2) t) 3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sum type whose override term does not mention the extra argument.

(acl2::must-succeed*
  (deftagsum rgb
    (:red ())
    (:green ())
    (:blue ())
    :pred rgbp)

  (deffold-reduce sz
    :types (rgb)
    :extra-args ((extra booleanp))
    :result natp
    :default 0
    :combine binary-+
    :override ((rgb 9))
    :name test)

  (assert-event (equal (rgb-sz (rgb-red) nil) 9))
  (assert-event (equal (rgb-sz (rgb-blue) t) 9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Sum/list types whose combination reduces to the default
; (and a list override) do not mention the extra argument,
; here in a mutually recursive clique.

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
    :extra-args ((extra booleanp))
    :result natp
    :default 0
    :combine binary-+
    :override
    ((foo :bar 1)
     (foo-list 5))
    :name test)

  ;; The list override term is used as the body of the list function,
  ;; regardless of the extra argument.
  (assert-event (equal (foo-list-count-bars nil nil) 5))
  (assert-event (equal (foo-list-count-bars (list (foo-bar) (foo-bar)) t) 5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Product type with a dependent requirement (:require),
; where the requirement is insensitive to the fixing of the fields.
; The generated theorem for the product constructor is conditional,
; with the requirement, applied to the type-fixed fields, as hypothesis.

(acl2::must-succeed*
  (deftagsum aexpr
    (:num ((val acl2::nat)))
    (:var ((name string))))

  (deflist aexpr-list
    :elt-type aexpr
    :true-listp t)

  (defprod bar
    ((elems aexpr-list :reqfix (if (consp elems)
                                   elems
                                 (list (aexpr-num 7)))))
    :require (consp elems))

  (deffold-reduce sum-vals
    :types (aexpr aexpr-list bar)
    :result natp
    :default 0
    :combine binary-+
    :override ((aexpr :num (aexpr-num->val aexpr)))
    :name test)

  ;; The generated conditional theorem applies
  ;; under the plain requirement,
  ;; because the requirement is insensitive to the fixing:
  (defruled bar-sum-vals-of-bar-applied
    (implies (consp elems)
             (equal (bar-sum-vals (bar elems))
                    (aexpr-list-sum-vals elems)))
    :enable bar-sum-vals-of-bar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Product type with a dependent requirement (:require),
; where the requirement is sensitive to the fixing of the fields:
; e.g. (< -1 0) holds but (< (nfix -1) (nfix 0)) does not.
; The hypothesis of the generated theorem for the product constructor
; must apply the requirement to the type-fixed fields:
; with the requirement applied to the unfixed fields,
; the formula would not be a theorem
; (see the counterexample theorem at the end).

(acl2::must-succeed*
  (deftagsum aexpr
    (:num ((val acl2::nat)))
    (:var ((name string))))

  (deflist aexpr-list
    :elt-type aexpr
    :true-listp t)

  (defprod foo
    ((lo acl2::nat)
     (hi acl2::nat :reqfix (if (< lo hi) hi (+ 1 lo)))
     (elems aexpr-list :reqfix (if (and (< lo hi) (consp elems))
                                   elems
                                 (list (aexpr-num 7)))))
    :require (and (< lo hi) (consp elems)))

  (deffold-reduce sum-vals
    :types (aexpr aexpr-list foo)
    :result natp
    :default 0
    :combine binary-+
    :override ((aexpr :num (aexpr-num->val aexpr)))
    :name test)

  ;; The generated conditional theorem applies
  ;; when the fields satisfy their types and the requirement:
  (defruled foo-sum-vals-of-foo-applied
    (implies (and (natp lo)
                  (natp hi)
                  (aexpr-list-p elems)
                  (< lo hi)
                  (consp elems))
             (equal (foo-sum-vals (foo lo hi elems))
                    (aexpr-list-sum-vals elems)))
    :enable (foo-sum-vals-of-foo nfix))

  ;; The requirement holds on these unfixed fields,
  ;; but the fold of the constructor differs from
  ;; the combination of the folds of the fields,
  ;; because the fixing of the fields falsifies the requirement,
  ;; and thus the constructor changes the fields via the :reqfix;
  ;; this shows that the generated theorem would not hold
  ;; with the requirement applied to the unfixed fields:
  (defrule foo-sum-vals-of-foo-not-with-unfixed-require
    (b* ((elems (list (aexpr-num 5))))
      (and (< -1 0)
           (consp elems)
           (not (equal (foo-sum-vals (foo -1 0 elems))
                       (aexpr-list-sum-vals elems)))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Product type with a dependent requirement (:require)
; whose associated :reqfix fixers only involve fields
; whose types have no fold functions:
; the generated theorem for the product constructor is unconditional,
; because the fold functions are not affected by the :reqfix fixers.

(acl2::must-succeed*
  (deftagsum aexpr
    (:num ((val acl2::nat)))
    (:var ((name string))))

  (deflist aexpr-list
    :elt-type aexpr
    :true-listp t)

  (defprod pair
    ((lo acl2::nat :reqfix (if (< lo hi) lo 0))
     (hi acl2::nat :reqfix (if (< lo hi) hi 1))
     (elems aexpr-list))
    :require (< lo hi))

  (deffold-reduce sum-vals
    :types (aexpr aexpr-list pair)
    :result natp
    :default 0
    :combine binary-+
    :override ((aexpr :num (aexpr-num->val aexpr)))
    :name test)

  ;; The generated theorem applies without any hypotheses:
  (defruled pair-sum-vals-of-pair-applied
    (equal (pair-sum-vals (pair lo hi elems))
           (aexpr-list-sum-vals elems))
    :enable pair-sum-vals-of-pair))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Summand of a sum type with a dependent requirement (:require),
; in a mutually recursive clique of types.
; Summands are treated like product types:
; the generated theorem for the summand constructor is conditional.

(acl2::must-succeed*
  (deftypes exprs
    (deftagsum expr
      (:const ((val acl2::nat)))
      (:call ((fn string)
              (args expr-list :reqfix (if (consp args)
                                          args
                                        (list (expr-fix nil)))))
       :require (consp args))
      :pred exprp)
    (deflist expr-list
      :elt-type expr
      :true-listp t
      :pred expr-listp))

  (deffold-reduce sum-consts
    :types (exprs)
    :result natp
    :default 0
    :combine binary-+
    :override ((expr :const (expr-const->val expr)))
    :name test)

  ;; The generated conditional theorem applies
  ;; under the plain requirement,
  ;; because the requirement is insensitive to the fixing:
  (defruled expr-sum-consts-of-expr-call-applied
    (implies (consp args)
             (equal (expr-sum-consts (expr-call fn args))
                    (expr-list-sum-consts args)))
    :enable expr-sum-consts-of-expr-call))
