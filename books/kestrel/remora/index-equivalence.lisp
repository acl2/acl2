; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")

(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ index-equivalence
  :parents (static-semantics)
  :short "Equivalence of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora involves
     the equivalence of indices used in types,
     which in turn determines the equivalence of types.
     Currently index equivalence in Remora is decidable,
     but the language may evolve towards undecidability.")
   (xdoc::p
    "The current (decidable) equivalence of indices
     is described in the arXiv paper and dissertation,
     in terms of normalization of indices:
     two indices are equivalent iff they normalize to the same index.
     We plan to formalize this notion at a higher level,
     and to prove that it is correct with respect to
     a suitable evaluation semantics of indices.
     We start by defining high-level executable code
     to normalize indices,
     and then define index equivalence based on that.
     We plan to verify the correctness of this normalization code."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sort-indices ((indices index-listp))
  :short "Sort a list of indices, using ACL2's total order of values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple insertion sort.
     We do not expect long lists."))
  :returns (sorted-indices index-listp)
  (cond ((endp indices) nil)
        (t (sort-indices-aux (car indices) (sort-indices (cdr indices)))))
  :verify-guards :after-returns
  :prepwork
  ((define sort-indices-aux ((index indexp) (indices index-listp))
     :returns (indices-with-index index-listp)
     :parents nil
     (cond ((endp indices) (list (index-fix index)))
           ((<< (index-fix index) (index-fix (car indices)))
            (cons (index-fix index) (index-list-fix indices)))
           (t (cons (index-fix (car indices))
                    (sort-indices-aux index (cdr indices))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-add-in-indices
  :short "Flatten all the nested additions in an index or list of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "For instance, @('(+ i (+ j k) (+ l) m (+ n (+ o p) q))')
     is turned into @('(+ i j k l m n o p q)')."))

  (define flatten-add-in-index ((index indexp))
    :returns (new-index indexp)
    :parents (index-equivalence flatten-add-in-indices)
    :short "Flatten all the nested additions in an index."
    :long
    (xdoc::topstring
     (xdoc::p
      "Variables and constants are left alone.
       For a shape or concatenation,
       we recursively flatten the additions in its components.
       For an addition, we recursively flatten the additions in the addends,
       and we also splice any resulting flattened sub-additions
       into the super-addition.
       For instance, given @('(+ i (+ (+ j k) l) 3)'),
       if we just flatten its components we get @('(+ i (+ j k l) 3)'),
       but then we also need to splice the sub-addition,
       obtaining @('(+ i j k l 3)').
       The splicing is done by @(tsee flatten-add-in-index-list),
       based on whether the @('addp') flag is @('t') or @('nil')."))
    (index-case
     index
     :var (index-var index.name)
     :const (index-const index.value)
     :shape (index-shape (flatten-add-in-index-list index.indices nil))
     :add (index-add (flatten-add-in-index-list index.indices t))
     :append (index-append (flatten-add-in-index-list index.indices nil)))
    :measure (index-count index))

  (define flatten-add-in-index-list ((indices index-listp) (addp booleanp))
    :returns (new-indices index-listp)
    :parents (index-equivalence flatten-add-in-indices)
    :short "Flatten all the nested additions in a list of indices,
            further flattening the resulting list if part of an addition."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through each index and flatten it.
       However, as explained in @(tsee flatten-add-in-index),
       we splice any obtained sub-addition into the current list,
       which is put into the super-addition by @(tsee flatten-add-in-index).
       The @('addp') flag is @('t') exactly when
       the indices passed to to this function are addends of an addition."))
    (b* (((when (endp indices)) nil)
         (new-index (flatten-add-in-index (car indices)))
         (new-indices (flatten-add-in-index-list (cdr indices) addp)))
      (if (and addp
               (index-case new-index :add))
          (append (index-add->indices new-index) new-indices)
        (cons new-index new-indices)))
    :measure (index-list-count indices))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual flatten-add-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define factor-consts-in-add-indices ((indices index-listp))
  :returns (mv (sum natp :rule-classes (:rewrite :type-prescription))
               (new-indices index-listp))
  :short "Collect and add all the constants in a list of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the indices of an addition index.
     It is intended for use after flattening additions
     via @(tsee flatten-add-in-indices).")
   (xdoc::p
    "We go through the indices,
     removing the constant ones and adding them to the running sum,
     and keeping the non-constant ones as they are.
     We retun the final sum and the non-constant indices;
     the latter are in the same order as in the original list."))
  (b* (((when (endp indices)) (mv 0 nil))
       (index (car indices))
       ((mv sum new-indices) (factor-consts-in-add-indices (cdr indices))))
    (if (index-case index :const)
        (mv (+ (index-const->value index) sum) new-indices)
      (mv sum (cons (index-fix index) new-indices))))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-add-indices ((indices index-listp))
  :returns (new-indices index-listp)
  :short "Normalize the indices of an addition index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is defined on arbitrary lists of indices,
     but it is intended for use on
     the indices of well-formed additions according to the typing rules,
     after all additions have been flattened via @(tsee flatten-add-in-indices).
     Under these conditions,
     the indices passed to this function
     consist of only constants and variables,
     without nested additions because of the flattening,
     and without shapes and concatenations because of the well-formedness.
     We factor the constants, we sort the variables,
     and we add a constant for the sum if it is not 0."))
  (b* (((mv sum indices) (factor-consts-in-add-indices indices))
       (indices (sort-indices indices)))
    (if (> sum 0)
        (cons (index-const sum) indices)
      indices)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines normalize-add-in-indices
  :short "Normalize additions in an index or list of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "We normalize the indices of all the additions;
     see @(tsee normalize-add-indices).
     We also replace empty additions with 0,
     and singleton additions with their only element."))

  (define normalize-add-in-index ((index indexp))
    :returns (new-index indexp)
    :parents (index-equivalence normalize-add-in-indices)
    :short "Normalize additions in an index."
    :long
    (xdoc::topstring
     (xdoc::p
      "For an addition index,
       we can avoid the recursive call of @(tsee normalize-add-in-index-list)
       because we always operate on well-formed indices after flattening,
       and thus the only components of an addition index
       are variable and constant indices."))
    (index-case
     index
     :var (index-var index.name)
     :const (index-const index.value)
     :shape (index-shape (normalize-add-in-index-list index.indices))
     :add (b* ((indices (normalize-add-indices index.indices))
               ((when (endp indices)) (index-const 0)) ; no indices
               ((when (endp (cdr indices))) (car indices))) ; one index
            (index-add indices)) ; two or more
     :append (index-append (normalize-add-in-index-list index.indices)))
    :measure (index-count index))

  (define normalize-add-in-index-list ((indices index-listp))
    :returns (new-indices index-listp)
    :parents (index-equivalence normalize-add-in-indices)
    :short "Normalize additions in a list of indices."
    (cond ((endp indices) nil)
          (t (cons (normalize-add-in-index (car indices))
                   (normalize-add-in-index-list (cdr indices)))))
    :measure (index-list-count indices))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual normalize-add-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define singleton-shapes ((indices index-listp))
  :returns (new-indices index-listp)
  :short "Wrap all the indices in a list into singleton shape indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each shape index with multiple indices
     must be turned into a concatenation of singleton shapes,
     e.g. @('(shape 2 d)') must be turned into @('(++ (shape 2) (shape d))').
     This function is called on the indices of the original shape index,
     and returns a list of wrapped singleton shapes."))
  (cond ((endp indices) nil)
        (t (cons (index-shape (list (car indices)))
                 (singleton-shapes (cdr indices))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines normalize-shape-in-indices
  :short "Normalize shapes in an index or list of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "We decompose shapes into concatenations of singleton shapes;
     see @(tsee singleton-shapes).
     If a shape has no dimensions,
     we turn it into the empty concatenation,
     to make it amenable to eventual elimination
     when part of a larger concatenation.
     If a shape is already a singleton, it is left unchanged.
     If a shape has two or more dimensions,
     it is turned into a concatenation of singletons."))

  (define normalize-shape-in-index ((index indexp))
    :returns (new-index indexp)
    :parents (index-equivalence normalize-shape-in-indices)
    :short "Normalize shapes in an index."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since well-formed shape and addition indices
       can only contain dimension indices,
       and not shape indices,
       we can avoid the recursive call of @(tsee normalize-shape-in-index-list)
       on the indices of a shape or addition index."))
    (index-case
     index
     :var (index-var index.name)
     :const (index-const index.value)
     :shape (if (and (consp index.indices)
                     (endp (cdr index.indices)))
                (index-shape index.indices)
              (index-append (singleton-shapes index.indices)))
     :add (index-add index.indices)
     :append (index-append (normalize-shape-in-index-list index.indices)))
    :measure (index-count index))

  (define normalize-shape-in-index-list ((indices index-listp))
    :returns (new-indices index-listp)
    :parents (index-equivalence normalize-shape-in-indices)
    :short "Normalize shapes in a list of indices."
    (cond ((endp indices) nil)
          (t (cons (normalize-shape-in-index (car indices))
                   (normalize-shape-in-index-list (cdr indices)))))
    :measure (index-list-count indices))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual normalize-shape-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines flatten-append-in-indices
  :short "Flatten all the nested concatenations in an index or list of indices."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee flatten-add-in-indices),
     but for concatenations instead of additions.
     See the documentation of those functions.")
   (xdoc::p
    "This is defined on all possible indices,
     but it is intended for use after normalizing shapes,
     which may produce concatenations.")
   (xdoc::p
    "The flattening of concatenations also has the effect of
     eliminating empty sub-concatenations used in super-concatenations,
     e.g. @('(++ i (++ j k) (++) l)') results in @('(++ i j k l)')."))

  (define flatten-append-in-index ((index indexp))
    :returns (new-index indexp)
    :parents (index-equivalence flatten-append-in-indices)
    :short "Flatten all the nested concatenations in an index."
    :long
    (xdoc::topstring
     (xdoc::p
      "In well-formed indices according to the typing rules,
       an addition or shape index cannot contain any concatenations.
       However, this function works on every index, not just well-formed ones.
       We just uniformly flatten all the nested concatenations."))
    (index-case
     index
     :var (index-var index.name)
     :const (index-const index.value)
     :add (index-add (flatten-append-in-index-list index.indices nil))
     :shape (index-shape (flatten-append-in-index-list index.indices nil))
     :append (index-append (flatten-append-in-index-list index.indices t)))
    :measure (index-count index))

  (define flatten-append-in-index-list ((indices index-listp)
                                        (appendp booleanp))
    :returns (new-indices index-listp)
    :parents (index-equivalence flatten-append-in-indices)
    :short "Flatten all the nested concatenations in a list of indices,
            further flattening the resulting list if part of a concatenation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The flag @('appendp') is analogous to
       @('addp') in @(tsee flatten-append-in-index).
       It is @('t') exactly when the indices are
       the components of a concatenation."))
    (b* (((when (endp indices)) nil)
         (new-index (flatten-append-in-index (car indices)))
         (new-indices (flatten-append-in-index-list (cdr indices) appendp)))
      (if (and appendp
               (index-case new-index :append))
          (append (index-append->indices new-index) new-indices)
        (cons new-index new-indices)))
    :measure (index-list-count indices))

  :verify-guards :after-returns

  ///

  (fty::deffixequiv-mutual flatten-append-in-indices))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define normalize-index ((index indexp))
  :short "Normalize an index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This defines the normalization of indices
     that we make to check their semantic equivalence,
     which in turn is used to check type equivalence.")
   (xdoc::p
    "We flatten and normalize all the additions.
     We normalize all the shapes.
     We flatten all the concatenations.")
   (xdoc::p
    "We need to prove that this does in fact normalize,
     in the sense that all and only the semantically equivalent indices
     normalize to the same form."))
  (b* ((index (flatten-add-in-index index))
       (index (normalize-add-in-index index))
       (index (normalize-shape-in-index index))
       (index (flatten-append-in-index index)))
    index))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define index-equivp ((index1 indexp) (index2 indexp))
  :returns (yes/no booleanp)
  :short "Check if two indices are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case iff they normalize to the same index."))
  (equal (normalize-index index1)
         (normalize-index index2)))
