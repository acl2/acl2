; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-structurals")

(include-book "kestrel/fty/deffold-reduce" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ispace-equivalence
  :parents (static-semantics)
  :short "Equivalence of ispaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora involves
     the equivalence of ispaces used in types,
     which in turn determines the equivalence of types.
     If we restrict dimensions to not use multiplication and subtraction,
     but only addition, then ispace equivalence in Remora is decidable,
     as described in [thesis].")
   (xdoc::p
    "[thesis] describes the decidable equivalence of ispaces
     in terms of normalization of ispaces:
     two ispaces are equivalent iff they normalize to the same ispace.
     We plan to formalize this notion at a higher level,
     and to prove that it is correct with respect to
     a suitable evaluation semantics of ispaces.
     We start by defining high-level executable code
     to normalize ispaces,
     and then define ispace equivalence based on that.
     We plan to verify the correctness of this normalization code.")
   (xdoc::p
    "We also plan to formalize a more general notion of equivalence,
     also involving multiplication and subtraction of dimensions,
     without necessarily requiring decidability.
     Indeed, Remora was planned to evolve towards undecidability,
     in order to capture stronger constraints via types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deffold-reduce addp
  :short "Check if a dimension or shape or ispace or a list thereof
          only contains addition, no multiplication or subtraction."
  :types (dims
          shapes
          ispace
          ispace-list)
  :result booleanp
  :default t
  :combine and
  :override
  ((dim :mul nil)
   (dim :sub nil))
  :name ispaces-addp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection addp-additional-theorems
  :short "Theorems about the @(see ispaces-addp) functions."

  (defruled dim-kind-not-mul-when-dim-addp
    (implies (dim-addp dim)
             (not (equal (dim-kind dim) :mul)))
    :rule-classes :forward-chaining
    :enable dim-addp)

  (defruled dim-kind-not-sub-when-dim-addp
    (implies (dim-addp dim)
             (not (equal (dim-kind dim) :sub)))
    :rule-classes :forward-chaining
    :enable dim-addp)

  (add-to-ruleset ispaces-addp-rules
                  '(dim-kind-not-mul-when-dim-addp
                    dim-kind-not-sub-when-dim-addp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* ispaces-addp-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sort-dims ((dims dim-listp))
  :returns (sorted-dims dim-listp)
  :short "Sort a list of dimensions, using ACL2's total order of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple insertion sort.
     We do not expect long lists."))
  (cond ((endp dims) nil)
        (t (sort-dims-aux (car dims) (sort-dims (cdr dims)))))
  :verify-guards :after-returns
  :prepwork
  ((define sort-dims-aux ((dim dimp) (dims dim-listp))
     :returns (dims-with-dim dim-listp)
     :parents nil
     (cond ((endp dims) (list (dim-fix dim)))
           ((<< (dim-fix dim) (dim-fix (car dims)))
            (cons (dim-fix dim) (dim-list-fix dims)))
           (t (cons (dim-fix (car dims))
                    (sort-dims-aux dim (cdr dims))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sort-shapes ((shapes shape-listp))
  :returns (sorted-shapes shape-listp)
  :short "Sort a list of shapes, using ACL2's total order of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple insertion sort.
     We do not expect long lists."))
  (cond ((endp shapes) nil)
        (t (sort-shapes-aux (car shapes) (sort-shapes (cdr shapes)))))
  :verify-guards :after-returns
  :prepwork
  ((define sort-shapes-aux ((shape shapep) (shapes shape-listp))
     :returns (shapes-with-shape shape-listp)
     :parents nil
     (cond ((endp shapes) (list (shape-fix shape)))
           ((<< (shape-fix shape) (shape-fix (car shapes)))
            (cons (shape-fix shape) (shape-list-fix shapes)))
           (t (cons (shape-fix (car shapes))
                    (sort-shapes-aux shape (cdr shapes))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-add-in-dims
  :short "Flatten all the nested additions
          in a dimension or list of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "For instance, @('(+ i (+ j k) (+ l) m (+ n (+ o p) q))')
     is turned into @('(+ i j k l m n o p q)')."))

  ;;;;;;;;;;;;;;;;;;;;

  (define flatten-add-in-dim ((dim dimp))
    :guard (dim-addp dim)
    :returns (new-dim dimp)
    :parents (ispace-equivalence flatten-add-in-dims)
    :short "Flatten all the nested additions in a dimension."
    :long
    (xdoc::topstring
     (xdoc::p
      "Variables and constants are left alone.
       For an addition, we recursively flatten the additions in the addends,
       and we also splice any resulting flattened sub-additions
       into the super-addition.
       For instance, given @('(+ i (+ (+ j k) l) 3)'),
       if we just flatten its components we get @('(+ i (+ j k l) 3)'),
       but then we also need to splice the sub-addition,
       obtaining @('(+ i j k l 3)').
       The splicing is done by @(tsee flatten-add-in-dim-list),
       based on whether the @('addp') flag is @('t') or @('nil')."))
    (dim-case
     dim
     :var (dim-var dim.name)
     :const (dim-const dim.val)
     :add (dim-add (flatten-add-in-dim-list dim.dims t))
     :mul (prog2$ (impossible) (dim-var "irrelevant"))
     :sub (prog2$ (impossible) (dim-var "irrelevant")))
    :measure (dim-count dim))

  ;;;;;;;;;;;;;;;;;;;;

  (define flatten-add-in-dim-list ((dims dim-listp) (addp booleanp))
    :guard (dim-list-addp dims)
    :returns (new-dims dim-listp)
    :parents (ispace-equivalence flatten-add-in-dims)
    :short "Flatten all the nested additions in a list of dimensions,
            further flattening the resulting list if part of an addition."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through each dimension and flatten it.
       However, as explained in @(tsee flatten-add-in-dim),
       we splice any obtained sub-addition into the current list,
       which is put into the super-addition by @(tsee flatten-add-in-dim).
       The @('addp') flag is @('t') exactly when
       the ispaces passed to this function are addends of an addition."))
    (b* (((when (endp dims)) nil)
         (new-dim (flatten-add-in-dim (car dims)))
         (new-dims (flatten-add-in-dim-list (cdr dims) addp)))
      (if (and addp
               (dim-case new-dim :add))
          (append (dim-add->dims new-dim) new-dims)
        (cons new-dim new-dims)))
    :measure (dim-list-count dims))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual flatten-add-in-dims)

  ;;;;;;;;;;;;;;;;;;;;

  (defret-mutual dim-addp-of-flatten-add-in-dims
    (defret dim-addp-of-flatten-add-in-dim
      (dim-addp new-dim)
      :hyp (dim-addp dim)
      :fn flatten-add-in-dim)
    (defret dim-list-addp-of-flatten-add-in-dim-list
      (dim-list-addp new-dims)
      :hyp (dim-list-addp dims)
      :fn flatten-add-in-dim-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define factor-consts-in-add-dims ((dims dim-listp))
  :returns (mv (sum natp :rule-classes (:rewrite :type-prescription))
               (new-dims dim-listp))
  :short "Collect and add all the constants in a list of dimensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the dimensions of an addition dimension.
     It is intended for use after flattening additions
     via @(tsee flatten-add-in-dims).")
   (xdoc::p
    "We go through the dimensions,
     removing the constant ones and adding them to the running sum,
     and keeping the non-constant ones as they are.
     We return the final sum and the non-constant dimensions;
     the latter are in the same order as in the original list."))
  (b* (((when (endp dims)) (mv 0 nil))
       (dim (car dims))
       ((mv sum new-dims) (factor-consts-in-add-dims (cdr dims))))
    (if (dim-case dim :const)
        (mv (+ (dim-const->val dim) sum) new-dims)
      (mv sum (cons (dim-fix dim) new-dims))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-add-dims ((dims dim-listp))
  :returns (new-dims dim-listp)
  :short "Normalize the dimensions of an addition dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is defined on arbitrary lists of dimensions,
     but it is intended for use
     after all additions have been flattened via @(tsee flatten-add-in-dims).
     Under these conditions,
     the dimensions passed to this function
     consist of only constants and variables,
     without nested additions because of the flattening.
     We factor the constants, we sort the variables,
     and we add a constant for the sum if it is not 0."))
  (b* (((mv sum dims) (factor-consts-in-add-dims dims))
       (dims (sort-dims dims)))
    (if (> sum 0)
        (cons (dim-const sum) dims)
      dims)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-add-in-dim ((dim dimp))
  :guard (dim-addp dim)
  :returns (new-dim dimp)
  :short "Normalize additions in a dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is intended for use
     after all additions have been flattened via @(tsee flatten-add-in-dims).
     We use @(tsee normalize-add-dims)
     to normalize the dimensions of all the additions.
     We also replace empty additions with 0,
     and singleton additions with their only element."))
  (dim-case
   dim
   :var (dim-var dim.name)
   :const (dim-const dim.val)
   :add (b* ((dims (normalize-add-dims dim.dims))
             ((when (endp dims)) (dim-const 0)) ; no dimensions
             ((when (endp (cdr dims))) (car dims))) ; one dimension
          (dim-add dims)) ; two or more dimensions
   :mul (prog2$ (impossible) (dim-var "irrelevant"))
   :sub (prog2$ (impossible) (dim-var "irrelevant"))))

;;;;;;;;;;;;;;;;;;;;

(define normalize-add-in-dim-list ((dims dim-listp))
  :guard (dim-list-addp dims)
  :returns (new-dims dim-listp)
  :short "Normalize additions in a list of dimensions."
  (cond ((endp dims) nil)
        (t (cons (normalize-add-in-dim (car dims))
                 (normalize-add-in-dim-list (cdr dims))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-dim ((dim dimp))
  :guard (dim-addp dim)
  :returns (new-dim dimp)
  :short "Normalize a dimension."
  :long
  (xdoc::topstring
   (xdoc::p
    "We flatten and normalize all the additions."))
  (normalize-add-in-dim (flatten-add-in-dim dim)))

;;;;;;;;;;;;;;;;;;;;

(define normalize-dim-list ((dims dim-listp))
  :guard (dim-list-addp dims)
  :returns (new-dims dim-listp)
  :short "Normalize a list of dimensions."
  (cond ((endp dims) nil)
        (t (cons (normalize-dim (car dims))
                 (normalize-dim-list (cdr dims))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines normalize-dims-in-shapes
  :short "Normalize dimensions in shapes and lists of shapes."

  ;;;;;;;;;;;;;;;;;;;;

  (define normalize-dims-in-shape ((shape shapep))
    :guard (shape-addp shape)
    :returns (new-shape shapep)
    :parents (ispace-equivalence normalize-dims-in-shapes)
    :short "Normalize dimensions in a shape."
    (shape-case
     shape
     :var (shape-var shape.name)
     :dim (shape-dim (normalize-dim shape.dim))
     :dims (shape-dims (normalize-dim-list shape.dims))
     :append (shape-append (normalize-dims-in-shape-list shape.shapes))
     :splice (shape-splice (normalize-dims-in-shape-list shape.shapes)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;

  (define normalize-dims-in-shape-list ((shapes shape-listp))
    :guard (shape-list-addp shapes)
    :returns (new-shapes shape-listp)
    :parents (ispace-equivalence normalize-dims-in-shapes)
    :short "Normalize dimensions in a list of shapes."
    (cond ((endp shapes) nil)
          (t (cons (normalize-dims-in-shape (car shapes))
                   (normalize-dims-in-shape-list (cdr shapes)))))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual normalize-dims-in-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines normalize-shapes-single-in-shapes
  :short "Normalize shapes to single dimensions in a shape or list of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose shapes into concatenations of single-dimension shapes;
     that is, we eliminate @(':dims') shapes
     in favor of concatenations of @(':dim') shapes.
     If a @(':dims') shape has no dimensions,
     we turn it into the empty concatenation.
     If a @(':dims') shape has one dimension,
     we convert it to a @(':dim') shape with that dimension.
     If a @(':dims') shape has two or more dimensions,
     we turn it into a concatenation of @(':dim') shapes,
     each of which contains one of the dimensions."))

  ;;;;;;;;;;;;;;;;;;;;

  (define normalize-shapes-single-in-shape ((shape shapep))
    :returns (new-shape shapep)
    :parents (ispace-equivalence normalize-shapes-single-in-shapes)
    :short "Normalize shapes to single dimensions in a shape."
    (shape-case
     shape
     :var (shape-var shape.name)
     :dim (shape-dim shape.dim)
     :dims (cond ((endp shape.dims) ; no dimensions
                  (shape-append nil))
                 ((endp (cdr shape.dims)) ; one dimension
                  (shape-dim (car shape.dims)))
                 (t ; two or more dimensions
                  (shape-append (shape-dim-list shape.dims))))
     :append (shape-append
              (normalize-shapes-single-in-shape-list shape.shapes))
     :splice (shape-splice
              (normalize-shapes-single-in-shape-list shape.shapes)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;

  (define normalize-shapes-single-in-shape-list ((shapes shape-listp))
    :returns (new-shapes shape-listp)
    :parents (ispace-equivalence normalize-shapes-single-in-shapes)
    :short "Normalize shapes to single dimensions in a list of shapes."
    (cond ((endp shapes) nil)
          (t (cons (normalize-shapes-single-in-shape (car shapes))
                   (normalize-shapes-single-in-shape-list (cdr shapes)))))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual normalize-shapes-single-in-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-append-in-shapes
  :short "Flatten all the nested concatenations in a shape or list of shapes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is partly analogous to @(tsee flatten-add-in-dims),
     but for shape concatenations instead of dimension additions;
     see the documentation of those functions.
     But while we flatten the concatenations,
     we also turn variables and shapes with dimensions
     into singleton concatenations,
     and we also turn splices into concatenations
     (as noted in @(tsee shape), splices and concatenations are equivalent).")
   (xdoc::p
    "This is defined on all possible shapes,
     but it is intended for use after normalizing shapes to single dimensions
     via @(tsee normalize-shapes-single-in-shapes),
     which may produce concatenations.")
   (xdoc::p
    "The flattening of concatenations also has the effect of
     eliminating empty sub-concatenations used in super-concatenations,
     e.g. @('(++ i (++ j k) (++) l)') results in @('(++ i j k l)')."))

  ;;;;;;;;;;;;;;;;;;;;

  (define flatten-append-in-shape ((shape shapep))
    :returns (new-shape shapep)
    :parents (ispace-equivalence flatten-append-in-shapes)
    :short "Flatten all the nested concatenations in a shape."
    (shape-case
     shape
     :var (shape-append (list (shape-var shape.name)))
     :dim (shape-append (list (shape-dim shape.dim)))
     :dims (shape-append (list (shape-dims shape.dims)))
     :append (shape-append (flatten-append-in-shape-list shape.shapes t))
     :splice (shape-append (flatten-append-in-shape-list shape.shapes t)))
    :measure (shape-count shape))

  ;;;;;;;;;;;;;;;;;;;;

  (define flatten-append-in-shape-list ((shapes shape-listp) (appendp booleanp))
    :returns (new-shapes shape-listp)
    :parents (ispace-equivalence flatten-append-in-shapes)
    :short "Flatten all the nested concatenations in a list of shapes,
            further flattening the resulting list if part of a concatenation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The flag @('appendp') is analogous to
       @('addp') in @(tsee flatten-add-in-dim-list).
       It is @('t') exactly when the shapes are
       the components of a concatenation (or splice)."))
    (b* (((when (endp shapes)) nil)
         (new-shape (flatten-append-in-shape (car shapes)))
         (new-shapes (flatten-append-in-shape-list (cdr shapes) appendp)))
      (if (and appendp
               (shape-case new-shape :append))
          (append (shape-append->shapes new-shape) new-shapes)
        (cons new-shape new-shapes)))
    :measure (shape-list-count shapes))

  ;;;;;;;;;;;;;;;;;;;;

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual flatten-append-in-shapes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-shape ((shape shapep))
  :guard (shape-addp shape)
  :returns (new-shape shapep)
  :short "Normalize a shape."
  :long
  (xdoc::topstring
   (xdoc::p
    "We normalize its dimensions,
     then we normalize shapes to have single dimensions,
     and finally we flatten all concatenations."))
  (b* ((shape (normalize-dims-in-shape shape))
       (shape (normalize-shapes-single-in-shape shape))
       (shape (flatten-append-in-shape shape)))
    shape))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define shape-equivp ((shape1 shapep) (shape2 shapep))
  :returns (yes/no booleanp)
  :short "Check if two shapes are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case iff they only use addition
     and they normalize to the same shape."))
  (and (shape-addp shape1)
       (shape-addp shape2)
       (equal (normalize-shape shape1)
              (normalize-shape shape2))))
