; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "renaming-evaluation")

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "arithmetic"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ value-groundness
  :parents (unique-names-validation)
  :short "Values that embed no abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most values carry no abstract syntax, but some do: the three kinds of
     lambda value embed the body of the abstraction, and the type values of
     universal, product, and sum types embed the body of the type.  A value
     that embeds none is called ground.")
   (xdoc::p
    "Renaming the variables of an expression (see @(see unique-names))
     touches only abstract syntax, and a ground value embeds none, so ground
     values are unaffected by renaming: on ground results, agreement modulo
     renaming is literal equality.  The proof of @(tsee eval-top-expr-of-expr-uniquify-names)
     uses groundness as the proviso of its main theorem and in the collapse
     of the witness-indexed value relation on ground values (see @(see
     uniquify-alpha-relations)), which compares ground values by plain
     equality.")
   (xdoc::p
    "The book also proves that the values the evaluator's array builders
     produce from ground elements are ground, and hence so are the results
     of the single-stage ispace primitives, and that the results of the
     scalar primitives, being base values, are ground."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Groundness of values: no embedded abstract syntax.

;; The type-values/denv clique includes the map from type variables to type
;; values (for the environments captured in type values), for which
;; DEFFOLD-REDUCE generates a theorem about the values of OMAP::ASSOC whose
;; proof needs OMAP::ASSOC to open; the macro provides no hints for it, so
;; we enable it locally around the fold.

(encapsulate ()

  (local (in-theory (enable omap::assoc)))

  (fty::deffold-reduce groundp
    :short "Check that a (type or expression) value embeds no abstract syntax."
    :long
    (xdoc::topstring
     (xdoc::p
      "Base values, primitive operations, and vectors of ground values are
       ground.  Lambda values (of all three kinds) are not, since they embed
       the abstract syntax of their bodies; neither are the type values of
       universal, product, and sum types, for the same reason.  The dynamic
       environments captured in the latter are reached by the fold but do
       not matter, since the type values containing them are never ground.")
     (xdoc::p
      "Ground values are unaffected by renaming the variables of the
       expression that produced them; this is the proviso under which
       evaluation results are literally equal in
       @('eval-top-expr-of-expr-uniquify-names')."))
    :types (type-values/denv
            expr-values/denv)
    :result booleanp
    :default t
    :combine and
    :override
    ((type-value :forall nil)
     (type-value :pi nil)
     (type-value :sigma nil)
     (expr-value :lambda nil)
     (expr-value :tlambda nil)
     (expr-value :ilambda nil))
    :name value-groundp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Groundness of the values built by the array builders from ground elements,
; and hence of the results of the single-stage ispace primitives; and of
; the results of the scalar primitives, which are base values.

; The fold functions stay closed in these proofs, which use the
; constructor rules of the fold instead.

(local (in-theory (disable expr-value-groundp
                           expr-value-list-groundp
                           primop-value-groundp
                           string-expr-value-map-groundp
                           expr-denv-groundp
                           type-value-groundp
                           type-value-list-groundp)))

(local (in-theory (enable expr-value-groundp-of-expr-value-base
                          expr-value-groundp-of-expr-value-box
                          expr-value-groundp-of-expr-value-primop
                          expr-value-groundp-of-expr-value-vector
                          expr-value-groundp-of-expr-value-vector-empty
                          type-value-groundp-of-type-value-array
                          type-value-groundp-of-type-value-base
                          type-value-groundp-of-type-value-fun)))

(defruled expr-value-list-groundp-of-expr-value-base-list
  (expr-value-list-groundp (expr-value-base-list vals))
  :induct t
  :enable (expr-value-base-list
           expr-value-list-groundp-of-cons
           expr-value-list-groundp-when-atom))

(local (in-theory (enable expr-value-list-groundp-of-expr-value-base-list)))

(local (in-theory (disable (:e tau-system))))

(local
 (defrule len-positive-when-consp-local
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear
   :expand ((len x))))

(defruled expr-value-list-groundp-of-repeat
  (implies (expr-value-groundp val)
           (expr-value-list-groundp (repeat n val)))
  :induct (repeat n val)
  :enable (repeat
           expr-value-list-groundp-of-cons
           expr-value-list-groundp-when-atom))

(defruled expr-value-groundp-of-expr-value-with-empty-dim
  (implies (type-value-groundp elem)
           (expr-value-groundp (expr-value-with-empty-dim dims elem)))
  :induct (expr-value-with-empty-dim dims elem)
  :enable (expr-value-with-empty-dim
           expr-value-list-groundp-of-repeat))

(defruled expr-value-list-groundp-of-nthcdr
  (implies (expr-value-list-groundp vals)
           (expr-value-list-groundp (nthcdr n vals)))
  :induct (nthcdr n vals)
  :enable (nthcdr
         len
           expr-value-list-groundp-when-atom
           expr-value-list-groundp-of-cdr-when-expr-value-list-groundp))

(encapsulate ()

  (local (include-book "arithmetic-3/top" :dir :system))
  (local (include-book "std/lists/take" :dir :system))
  (local (include-book "std/lists/nthcdr" :dir :system))

  ; The take/nthcdr inductions below need this rule off.
  (local (in-theory (disable acl2::nthcdr-of-cdr)))

  (defruled expr-value-list-groundp-of-take
    (implies (and (expr-value-list-groundp vals)
                  (<= (nfix n) (len vals)))
             (expr-value-list-groundp (take n vals)))
    :induct (take n vals)
    :enable (take
             expr-value-list-groundp-of-cons
             expr-value-list-groundp-when-atom
             expr-value-groundp-of-car-when-expr-value-list-groundp
             expr-value-list-groundp-of-cdr-when-expr-value-list-groundp))

  (define expr-value-list-list-groundp ((valss expr-value-list-listp))
    :returns (yes/no booleanp)
    (or (endp valss)
        (and (expr-value-list-groundp (car valss))
             (expr-value-list-list-groundp (cdr valss)))))

  (defruled expr-value-list-list-groundp-of-list-split
    (implies (and (expr-value-list-groundp vals)
                  (posp chunk)
                  (integerp (/ (len vals) chunk)))
             (expr-value-list-list-groundp (list-split vals chunk)))
    :induct (list-split vals chunk)
    :enable (list-split
             expr-value-list-list-groundp
             expr-value-list-groundp-of-take
             expr-value-list-groundp-of-nthcdr
             fix nfix
             lt-to-zero-when-divided-by-pos)
    :hints ('(:use (:instance integerp-of-div-of-diff
                              (x (len vals))
                              (c (pos-fix chunk))))))

  ; The chunking performed by the builders is exact (as in the proofs about
  ; the same builders in EXPRESSION-VALUES-AND-ENVIRONMENTS, whose
  ; POSP-OF-LEN-OVER-CAR-OF-DIMS is used here too).

  (defruledl chunk-divides-lemma
    (implies (and (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims)
                  (equal (len vals) (nat-list-product dims)))
             (integerp (/ (len vals) (* (/ (car dims)) (len vals)))))
    :use nat-list-product-divided-by-car)

  (defruledl expr-value-list-list-groundp-of-list-split-chunk
    (implies (and (nat-listp dims)
                  (not (member-equal 0 dims))
                  (consp dims)
                  (equal (len vals) (nat-list-product dims))
                  (expr-value-list-groundp vals))
             (expr-value-list-list-groundp
              (list-split vals (* (/ (car dims)) (len vals)))))
    :use ((:instance expr-value-list-list-groundp-of-list-split
                     (chunk (* (/ (car dims)) (len vals))))
          posp-of-len-over-car-of-dims
          chunk-divides-lemma))

  (defthm-expr-values-with-nonempty-dims-flag
    (defthm expr-value-groundp-of-expr-value-with-nonempty-dims
      (implies (and (nat-listp dims)
                    (expr-value-listp vals)
                    (not (member-equal 0 dims))
                    (equal (len vals) (nat-list-product dims))
                    (expr-value-list-groundp vals))
               (expr-value-groundp (expr-value-with-nonempty-dims dims vals)))
      :flag expr-value-with-nonempty-dims)
    (defthm expr-value-list-groundp-of-expr-value-list-with-nonempty-dims
      (implies (and (nat-listp dims)
                    (expr-value-list-listp valss)
                    (not (member-equal 0 dims))
                    (all-of-len-p valss (nat-list-product dims))
                    (expr-value-list-list-groundp valss))
               (expr-value-list-groundp
                (expr-value-list-with-nonempty-dims dims valss)))
      :flag expr-value-list-with-nonempty-dims)
    :hints (("Goal"
             :in-theory (enable expr-value-with-nonempty-dims
                                expr-value-list-with-nonempty-dims
                                expr-value-list-list-groundp
                                expr-value-list-list-groundp-of-list-split-chunk
                                expr-value-list-groundp-of-cons
                                expr-value-list-groundp-when-atom
                                expr-value-groundp-of-car-when-expr-value-list-groundp
                                all-of-len-p
                                nat-list-product-of-cdr-to-ratio
                                pos-fix
                                posp-of-len-over-car-of-dims))))

  (in-theory (disable expr-value-groundp-of-expr-value-with-nonempty-dims
                      expr-value-list-groundp-of-expr-value-list-with-nonempty-dims))

  (defruled expr-value-groundp-of-prim-iota/static
    (expr-value-groundp (prim-iota/static s))
    :enable (prim-iota/static
             expr-value-groundp-of-expr-value-with-empty-dim
             nfix fix)
    :use ((:instance expr-value-groundp-of-expr-value-with-nonempty-dims
                     (dims (nat-list-fix s))
                     (vals (expr-value-base-list
                            (base-value-int-list
                             (int-value-list-of
                              (nat-list-from-to
                               0 (nat-list-product (nat-list-fix s)))))))))))

(defruled expr-value-groundp-of-prim-reify-dim
  (expr-value-groundp (prim-reify-dim d))
  :enable prim-reify-dim)

(defruled expr-value-groundp-of-prim-int-add
  (implies (not (reserrp (prim-int-add val1 val2)))
           (expr-value-groundp (prim-int-add val1 val2)))
  :enable prim-int-add)

(defruled expr-value-groundp-of-prim-int-sub
  (implies (not (reserrp (prim-int-sub val1 val2)))
           (expr-value-groundp (prim-int-sub val1 val2)))
  :enable prim-int-sub)

(defruled expr-value-groundp-of-prim-int-mul
  (implies (not (reserrp (prim-int-mul val1 val2)))
           (expr-value-groundp (prim-int-mul val1 val2)))
  :enable prim-int-mul)

(defruled expr-value-groundp-of-prim-int-div
  (implies (not (reserrp (prim-int-div val1 val2)))
           (expr-value-groundp (prim-int-div val1 val2)))
  :enable prim-int-div)

(defruled expr-value-groundp-of-prim-int-expt
  (implies (not (reserrp (prim-int-expt val1 val2)))
           (expr-value-groundp (prim-int-expt val1 val2)))
  :enable prim-int-expt)

(defruled expr-value-groundp-of-prim-int-mod
  (implies (not (reserrp (prim-int-mod val1 val2)))
           (expr-value-groundp (prim-int-mod val1 val2)))
  :enable prim-int-mod)

(defruled expr-value-groundp-of-prim-int-max
  (implies (not (reserrp (prim-int-max val1 val2)))
           (expr-value-groundp (prim-int-max val1 val2)))
  :enable prim-int-max)

(defruled expr-value-groundp-of-prim-int-min
  (implies (not (reserrp (prim-int-min val1 val2)))
           (expr-value-groundp (prim-int-min val1 val2)))
  :enable prim-int-min)

(defruled expr-value-groundp-of-prim-int-bit-and
  (implies (not (reserrp (prim-int-bit-and val1 val2)))
           (expr-value-groundp (prim-int-bit-and val1 val2)))
  :enable prim-int-bit-and)

(defruled expr-value-groundp-of-prim-int-bit-or
  (implies (not (reserrp (prim-int-bit-or val1 val2)))
           (expr-value-groundp (prim-int-bit-or val1 val2)))
  :enable prim-int-bit-or)

(defruled expr-value-groundp-of-prim-int-bit-xor
  (implies (not (reserrp (prim-int-bit-xor val1 val2)))
           (expr-value-groundp (prim-int-bit-xor val1 val2)))
  :enable prim-int-bit-xor)

(defruled expr-value-groundp-of-prim-int-shl
  (implies (not (reserrp (prim-int-shl val1 val2)))
           (expr-value-groundp (prim-int-shl val1 val2)))
  :enable prim-int-shl)

(defruled expr-value-groundp-of-prim-int-shr
  (implies (not (reserrp (prim-int-shr val1 val2)))
           (expr-value-groundp (prim-int-shr val1 val2)))
  :enable prim-int-shr)

(defruled expr-value-groundp-of-prim-int-bit-not
  (implies (not (reserrp (prim-int-bit-not val1)))
           (expr-value-groundp (prim-int-bit-not val1)))
  :enable prim-int-bit-not)

(defruled expr-value-groundp-of-prim-int-popc
  (implies (not (reserrp (prim-int-popc val1)))
           (expr-value-groundp (prim-int-popc val1)))
  :enable prim-int-popc)

(defruled expr-value-groundp-of-prim-int-eq
  (implies (not (reserrp (prim-int-eq val1 val2)))
           (expr-value-groundp (prim-int-eq val1 val2)))
  :enable prim-int-eq)

(defruled expr-value-groundp-of-prim-int-neq
  (implies (not (reserrp (prim-int-neq val1 val2)))
           (expr-value-groundp (prim-int-neq val1 val2)))
  :enable prim-int-neq)

(defruled expr-value-groundp-of-prim-int-lt
  (implies (not (reserrp (prim-int-lt val1 val2)))
           (expr-value-groundp (prim-int-lt val1 val2)))
  :enable prim-int-lt)

(defruled expr-value-groundp-of-prim-int-gt
  (implies (not (reserrp (prim-int-gt val1 val2)))
           (expr-value-groundp (prim-int-gt val1 val2)))
  :enable prim-int-gt)

(defruled expr-value-groundp-of-prim-int-leq
  (implies (not (reserrp (prim-int-leq val1 val2)))
           (expr-value-groundp (prim-int-leq val1 val2)))
  :enable prim-int-leq)

(defruled expr-value-groundp-of-prim-int-geq
  (implies (not (reserrp (prim-int-geq val1 val2)))
           (expr-value-groundp (prim-int-geq val1 val2)))
  :enable prim-int-geq)

(defruled expr-value-groundp-of-prim-int-to-float
  (implies (not (reserrp (prim-int-to-float val1)))
           (expr-value-groundp (prim-int-to-float val1)))
  :enable prim-int-to-float)

(defruled expr-value-groundp-of-prim-int-to-bool
  (implies (not (reserrp (prim-int-to-bool val1)))
           (expr-value-groundp (prim-int-to-bool val1)))
  :enable prim-int-to-bool)

(defruled expr-value-groundp-of-prim-float-add
  (implies (not (reserrp (prim-float-add val1 val2)))
           (expr-value-groundp (prim-float-add val1 val2)))
  :enable prim-float-add)

(defruled expr-value-groundp-of-prim-float-sub
  (implies (not (reserrp (prim-float-sub val1 val2)))
           (expr-value-groundp (prim-float-sub val1 val2)))
  :enable prim-float-sub)

(defruled expr-value-groundp-of-prim-float-mul
  (implies (not (reserrp (prim-float-mul val1 val2)))
           (expr-value-groundp (prim-float-mul val1 val2)))
  :enable prim-float-mul)

(defruled expr-value-groundp-of-prim-float-div
  (implies (not (reserrp (prim-float-div val1 val2)))
           (expr-value-groundp (prim-float-div val1 val2)))
  :enable prim-float-div)

(defruled expr-value-groundp-of-prim-float-expt
  (implies (not (reserrp (prim-float-expt val1 val2)))
           (expr-value-groundp (prim-float-expt val1 val2)))
  :enable prim-float-expt)

(defruled expr-value-groundp-of-prim-float-max
  (implies (not (reserrp (prim-float-max val1 val2)))
           (expr-value-groundp (prim-float-max val1 val2)))
  :enable prim-float-max)

(defruled expr-value-groundp-of-prim-float-min
  (implies (not (reserrp (prim-float-min val1 val2)))
           (expr-value-groundp (prim-float-min val1 val2)))
  :enable prim-float-min)

(defruled expr-value-groundp-of-prim-float-sqrt
  (implies (not (reserrp (prim-float-sqrt val1)))
           (expr-value-groundp (prim-float-sqrt val1)))
  :enable prim-float-sqrt)

(defruled expr-value-groundp-of-prim-float-eq
  (implies (not (reserrp (prim-float-eq val1 val2)))
           (expr-value-groundp (prim-float-eq val1 val2)))
  :enable prim-float-eq)

(defruled expr-value-groundp-of-prim-float-neq
  (implies (not (reserrp (prim-float-neq val1 val2)))
           (expr-value-groundp (prim-float-neq val1 val2)))
  :enable prim-float-neq)

(defruled expr-value-groundp-of-prim-float-lt
  (implies (not (reserrp (prim-float-lt val1 val2)))
           (expr-value-groundp (prim-float-lt val1 val2)))
  :enable prim-float-lt)

(defruled expr-value-groundp-of-prim-float-gt
  (implies (not (reserrp (prim-float-gt val1 val2)))
           (expr-value-groundp (prim-float-gt val1 val2)))
  :enable prim-float-gt)

(defruled expr-value-groundp-of-prim-float-leq
  (implies (not (reserrp (prim-float-leq val1 val2)))
           (expr-value-groundp (prim-float-leq val1 val2)))
  :enable prim-float-leq)

(defruled expr-value-groundp-of-prim-float-geq
  (implies (not (reserrp (prim-float-geq val1 val2)))
           (expr-value-groundp (prim-float-geq val1 val2)))
  :enable prim-float-geq)

(defruled expr-value-groundp-of-prim-float-truncate
  (implies (not (reserrp (prim-float-truncate val1)))
           (expr-value-groundp (prim-float-truncate val1)))
  :enable prim-float-truncate)

(defruled expr-value-groundp-of-prim-float-round
  (implies (not (reserrp (prim-float-round val1)))
           (expr-value-groundp (prim-float-round val1)))
  :enable prim-float-round)

(defruled expr-value-groundp-of-prim-float-ceiling
  (implies (not (reserrp (prim-float-ceiling val1)))
           (expr-value-groundp (prim-float-ceiling val1)))
  :enable prim-float-ceiling)

(defruled expr-value-groundp-of-prim-float-floor
  (implies (not (reserrp (prim-float-floor val1)))
           (expr-value-groundp (prim-float-floor val1)))
  :enable prim-float-floor)

(defruled expr-value-groundp-of-prim-bool-not
  (implies (not (reserrp (prim-bool-not val1)))
           (expr-value-groundp (prim-bool-not val1)))
  :enable prim-bool-not)

(defruled expr-value-groundp-of-prim-bool-and
  (implies (not (reserrp (prim-bool-and val1 val2)))
           (expr-value-groundp (prim-bool-and val1 val2)))
  :enable prim-bool-and)

(defruled expr-value-groundp-of-prim-bool-or
  (implies (not (reserrp (prim-bool-or val1 val2)))
           (expr-value-groundp (prim-bool-or val1 val2)))
  :enable prim-bool-or)

(defruled expr-value-groundp-of-prim-bool-eq
  (implies (not (reserrp (prim-bool-eq val1 val2)))
           (expr-value-groundp (prim-bool-eq val1 val2)))
  :enable prim-bool-eq)

(defruled expr-value-groundp-of-prim-bool-neq
  (implies (not (reserrp (prim-bool-neq val1 val2)))
           (expr-value-groundp (prim-bool-neq val1 val2)))
  :enable prim-bool-neq)

(defruled expr-value-groundp-of-prim-bool-to-int
  (implies (not (reserrp (prim-bool-to-int val1)))
           (expr-value-groundp (prim-bool-to-int val1)))
  :enable prim-bool-to-int)

(defruled expr-value-groundp-of-prim-bool-to-float
  (implies (not (reserrp (prim-bool-to-float val1)))
           (expr-value-groundp (prim-bool-to-float val1)))
  :enable prim-bool-to-float)
