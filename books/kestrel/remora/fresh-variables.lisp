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

(include-book "kestrel/fty/string-set" :dir :system)

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/basic/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ fresh-variables
  :parents (abstract-syntax)
  :short "Generation of fresh variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "For certain purposes, we need to generate fresh variables,
     i.e. variables that do not occur in a given set.
     This is easy to do and show correct, intuitively:
     we attempt to generate distinct variables from increasing numeric indices,
     until we find one not in the given set.
     The process terminates because the given set is finite.
     But it takes a little machinery to prove termination in the theorem prover,
     which we do here.")
   (xdoc::p
    "We provide this for ispace, type, and expression variables."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-lt-when-subset-and-not-member
  :short "Key theorem in the termination argument for fresh variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a general theorem about sets,
     which belongs to a more general library.")
   (xdoc::p
    "If we have two sets, one subset of the other,
     but there is some element in the second but not in the first,
     then the subset inclusion is strict,
     and so is the inequality between cardinalities.")
   (xdoc::p
    "In the loop that attempts to generate a fresh variable:
     @('a') is the variable generated in the current iteration,
     which is still in the set of variables to avoid,
     so that we need to do another loop iteration;
     @('y') is the difference between the set to avoid
     and the variables generated so far, excluding @('a');
     and @('x') is obtained by removing @('a') from @('y').
     The measure of the loop is the cardinality of
     the set of variables to avoid minus those generated so far,
     i.e. @('y') in the current loop iteration
     and @('x') in the subsequent loop iteration.
     So this theorem serves to show that the measure decreases."))
  (implies (and (set::subset x y)
                (set::in a y)
                (not (set::in a x)))
           (< (set::cardinality x)
              (set::cardinality y)))
  :cases ((set::subset y x))
  :enable set::expensive-rules)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-dim-with-index ((prefix stringp) (index natp))
  :returns (var ispace-varp)
  :short "Generate a dimension ispace variable
          from a prefix and a numeric index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In concrete syntax,
     the variable would have the form @('$<p><i>'),
     where @('<p>') is the prefix and @('<i>') is the index.
     If the prefix is a legal Remora identifier,
     so is the generated variable's name.
     A key property is that it is an injective mapping given a prefix:
     different indices yield different variables."))
  (ispace-var-dim (str::cat prefix (str::nat-to-dec-string (lnfix index))))

  ///

  (defret ispace-var-dim-of-ispace-var-dim-with-index
    (equal (ispace-var-kind var) :dim))

  (defrule ispace-var-dim-with-index-injective
    (equal (equal (ispace-var-dim-with-index prefix index1)
                  (ispace-var-dim-with-index prefix index2))
           (equal (nfix index1)
                  (nfix index2)))
    :enable string-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-vars-dim-with-index-below ((prefix stringp) (index natp))
  :returns (vars ispace-var-setp)
  :short "Generate the set of dimension ispace variables
          with a given prefix for all the numeric indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to remove, from the set of variables to be avoided,
     all the failed attempts at generating a fresh variable.")
   (xdoc::p
    "Membership and subset reduce to index comparison;
     the injectivity of @(tsee ispace-var-dim-with-index) is needed here.
     This function is also injective."))
  (b* (((when (zp index)) nil)
       (index (1- index)))
    (set::insert (ispace-var-dim-with-index prefix index)
                 (ispace-vars-dim-with-index-below prefix index)))
  :verify-guards :after-returns
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defrule ispace-var-dim-with-index-in-set-below
    (equal (set::in (ispace-var-dim-with-index prefix index1)
                    (ispace-vars-dim-with-index-below prefix index2))
           (< (nfix index1)
              (nfix index2)))
    :induct t
    :enable nfix)

  (defrule ispace-vars-dim-with-index-below-subset
    (equal (set::subset (ispace-vars-dim-with-index-below prefix index1)
                        (ispace-vars-dim-with-index-below prefix index2))
           (<= (nfix index1) (nfix index2)))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defrule if-part
       (implies (<= (nfix index1) (nfix index2))
                (set::subset (ispace-vars-dim-with-index-below prefix index1)
                             (ispace-vars-dim-with-index-below prefix index2)))
       :induct t)
     (defrule only-if-part
       (implies (set::subset (ispace-vars-dim-with-index-below prefix index1)
                             (ispace-vars-dim-with-index-below prefix index2))
                (<= (nfix index1) (nfix index2)))
       :induct t
       :enable nfix)))

  (defrule ispace-vars-dim-with-index-below-injective
    (implies (equal (ispace-vars-dim-with-index-below prefix index1)
                    (ispace-vars-dim-with-index-below prefix index2))
             (equal (nfix index1) (nfix index2)))
    :enable set::double-containment-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-ispace-vars-dim-below-index ((prefix stringp)
                                            (index natp)
                                            (vars ispace-var-setp))
  :returns (new-vars ispace-var-setp)
  :short "Remove, from a set of ispace variables,
          all the dimension ispace variables
          with a given prefix and with indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the termination argument for generating fresh variables,
     the set @('vars') is the one to be avoided.
     So when we remove the variables below the index,
     we remove all the variables attempted so far."))
  (set::difference (ispace-var-set-fix vars)
                   (ispace-vars-dim-with-index-below prefix index))

  ///

  (defrule ispace-var-dim-with-index-in-remove-ispace-vars-dims-below-index
    (equal (set::in (ispace-var-dim-with-index prefix index1)
                    (remove-ispace-vars-dim-below-index prefix index2 vars))
           (and (set::in (ispace-var-dim-with-index prefix index1)
                         (ispace-var-set-fix vars))
                (>= (nfix index1) (nfix index2)))))

  (defrule remove-ispace-vars-dim-below-index-subset-when-index-leq
    (implies (>= (nfix index1) (nfix index2))
             (set::subset
              (remove-ispace-vars-dim-below-index prefix index1 vars)
              (remove-ispace-vars-dim-below-index prefix index2 vars)))
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-dim-ispace-var ((prefix stringp) (used ispace-var-setp))
  :returns (var ispace-varp)
  :short "Generate a fresh dimension ispace variable,
          i.e. one not in the set of already used ispace variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the approach in @(see fresh-variables).
     The termination lemma relies on the set theorem explained earlier."))
  (fresh-dim-ispace-var-loop prefix 0 used)

  :prepwork
  ((define fresh-dim-ispace-var-loop ((prefix stringp)
                                      (index natp)
                                      (used ispace-var-setp))
     :returns (var ispace-varp)
     :parents nil
     (b* ((var (ispace-var-dim-with-index prefix index)))
       (if (set::in var (ispace-var-set-fix used))
           (fresh-dim-ispace-var-loop prefix (1+ (lnfix index)) used)
         var))
     :measure (set::cardinality
               (remove-ispace-vars-dim-below-index prefix index used))
     :prepwork
     ((defrulel termination-lemma
        (implies (set::in (ispace-var-dim-with-index prefix index)
                          (ispace-var-set-fix vars))
                 (< (set::cardinality
                     (remove-ispace-vars-dim-below-index prefix
                                                         (1+ (nfix index))
                                                         vars))
                    (set::cardinality
                     (remove-ispace-vars-dim-below-index prefix
                                                         index
                                                         vars))))
        :use (:instance
              cardinality-lt-when-subset-and-not-member
              (x (remove-ispace-vars-dim-below-index prefix
                                                     (1+ (nfix index))
                                                     vars))
              (y (remove-ispace-vars-dim-below-index prefix
                                                     index
                                                     vars))
              (a (ispace-var-dim-with-index prefix index)))))

     ///

     (defret ispace-var-dim-of-fresh-dim-ispace-var-loop
       (equal (ispace-var-kind var) :dim)
       :hints (("Goal" :induct t)))

     (defret fresh-dim-ispace-var-loop-is-fresh
       (not (set::in var (ispace-var-set-fix used)))
       :hints (("Goal" :induct t)))))

  ///

  (defret ispace-var-dim-of-fresh-dim-ispace-var
    (equal (ispace-var-kind var) :dim))

  (defret fresh-dim-ispace-var-is-fresh
    (not (set::in var (ispace-var-set-fix used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-var-shape-with-index ((prefix stringp) (index natp))
  :returns (var ispace-varp)
  :short "Generate a shape ispace variable
          from a prefix and a numeric index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In concrete syntax,
     the variable would have the form @('@<p><i>'),
     where @('<p>') is the prefix and @('<i>') is the index.
     If the prefix is a legal Remora identifier,
     so is the generated variable's name.
     A key property is that it is an injective mapping:
     different indices yield different variables."))
  (ispace-var-shape (str::cat prefix (str::nat-to-dec-string (lnfix index))))

  ///

  (defret ispace-var-shape-of-ispace-var-shape-with-index
    (equal (ispace-var-kind var) :shape))

  (defrule ispace-var-shape-with-index-injective
    (equal (equal (ispace-var-shape-with-index prefix index1)
                  (ispace-var-shape-with-index prefix index2))
           (equal (nfix index1)
                  (nfix index2)))
    :enable string-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ispace-vars-shape-with-index-below ((prefix stringp) (index natp))
  :returns (vars ispace-var-setp)
  :short "Generate the set of shape ispace variables
          with a given prefix for all the numeric indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to remove, from the set of variables to be avoided,
     all the failed attempts at generating a fresh variable.")
   (xdoc::p
    "Membership and subset reduce to index comparison;
     the injectivity of @(tsee ispace-var-shape-with-index) is needed here.
     This function is also injective."))
  (b* (((when (zp index)) nil)
       (index (1- index)))
    (set::insert (ispace-var-shape-with-index prefix index)
                 (ispace-vars-shape-with-index-below prefix index)))
  :verify-guards :after-returns
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defrule ispace-var-shape-with-index-in-set-below
    (equal (set::in (ispace-var-shape-with-index prefix index1)
                    (ispace-vars-shape-with-index-below prefix index2))
           (< (nfix index1)
              (nfix index2)))
    :induct t
    :enable nfix)

  (defrule ispace-vars-shape-with-index-below-subset
    (equal (set::subset (ispace-vars-shape-with-index-below prefix index1)
                        (ispace-vars-shape-with-index-below prefix index2))
           (<= (nfix index1) (nfix index2)))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defrule if-part
       (implies (<= (nfix index1) (nfix index2))
                (set::subset
                 (ispace-vars-shape-with-index-below prefix index1)
                 (ispace-vars-shape-with-index-below prefix index2)))
       :induct t)
     (defrule only-if-part
       (implies (set::subset (ispace-vars-shape-with-index-below prefix index1)
                             (ispace-vars-shape-with-index-below prefix index2))
                (<= (nfix index1) (nfix index2)))
       :induct t
       :enable nfix)))

  (defrule ispace-vars-shape-with-index-below-injective
    (implies (equal (ispace-vars-shape-with-index-below prefix index1)
                    (ispace-vars-shape-with-index-below prefix index2))
             (equal (nfix index1) (nfix index2)))
    :enable set::double-containment-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-ispace-vars-shape-below-index ((prefix stringp)
                                              (index natp)
                                              (vars ispace-var-setp))
  :returns (new-vars ispace-var-setp)
  :short "Remove, from a set of ispace variables,
          all the shape ispace variables
          with a given prefix and with indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the termination argument for generating fresh variables,
     the set @('vars') is the one to be avoided.
     So when we remove the variables below the index,
     we remove all the variables attempted so far."))
  (set::difference (ispace-var-set-fix vars)
                   (ispace-vars-shape-with-index-below prefix index))

  ///

  (defrule ispace-var-shape-with-index-in-remove-ispace-vars-shapes-below-index
    (equal (set::in (ispace-var-shape-with-index prefix index1)
                    (remove-ispace-vars-shape-below-index prefix index2 vars))
           (and (set::in (ispace-var-shape-with-index prefix index1)
                         (ispace-var-set-fix vars))
                (>= (nfix index1) (nfix index2)))))

  (defrule remove-ispace-vars-shape-below-index-subset-when-index-leq
    (implies (>= (nfix index1) (nfix index2))
             (set::subset
              (remove-ispace-vars-shape-below-index prefix index1 vars)
              (remove-ispace-vars-shape-below-index prefix index2 vars)))
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-shape-ispace-var ((prefix stringp) (used ispace-var-setp))
  :returns (var ispace-varp)
  :short "Generate a fresh shape ispace variable,
          i.e. one not in the set of already used ispace variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the approach in @(see fresh-variables).
     The termination lemma relies on the set theorem explained earlier."))
  (fresh-shape-ispace-var-loop prefix 0 used)

  :prepwork
  ((define fresh-shape-ispace-var-loop ((prefix stringp)
                                        (index natp)
                                        (used ispace-var-setp))
     :returns (var ispace-varp)
     :parents nil
     (b* ((var (ispace-var-shape-with-index prefix index)))
       (if (set::in var (ispace-var-set-fix used))
           (fresh-shape-ispace-var-loop prefix (1+ (lnfix index)) used)
         var))
     :measure (set::cardinality
               (remove-ispace-vars-shape-below-index prefix index used))
     :prepwork
     ((defrulel termination-lemma
        (implies (set::in (ispace-var-shape-with-index prefix index)
                          (ispace-var-set-fix vars))
                 (< (set::cardinality
                     (remove-ispace-vars-shape-below-index prefix
                                                           (1+ (nfix index))
                                                           vars))
                    (set::cardinality
                     (remove-ispace-vars-shape-below-index prefix
                                                           index
                                                           vars))))
        :use (:instance
              cardinality-lt-when-subset-and-not-member
              (x (remove-ispace-vars-shape-below-index prefix
                                                       (1+ (nfix index))
                                                       vars))
              (y (remove-ispace-vars-shape-below-index prefix
                                                       index
                                                       vars))
              (a (ispace-var-shape-with-index prefix index)))))

     ///

     (defret ispace-var-shape-of-fresh-shape-ispace-var-loop
       (equal (ispace-var-kind var) :shape)
       :hints (("Goal" :induct t)))

     (defret fresh-shape-ispace-var-loop-is-fresh
       (not (set::in var (ispace-var-set-fix used)))
       :hints (("Goal" :induct t)))))

  ///

  (defret ispace-var-shape-of-fresh-shape-ispace-var
    (equal (ispace-var-kind var) :shape))

  (defret fresh-shape-ispace-var-is-fresh
    (not (set::in var (ispace-var-set-fix used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var-atom-with-index ((prefix stringp) (index natp))
  :returns (var type-varp)
  :short "Generate an atom type variable
          from a prefix and a numeric index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In concrete syntax,
     the variable would have the form @('&<p><i>'),
     where @('<p>') is the prefix and @('<i>') is the index.
     If the prefix is a legal Remora identifier,
     so is the generated variable's name.
     A key property is that it is an injective mapping:
     different indices yield different variables."))
  (type-var-atom (str::cat prefix (str::nat-to-dec-string (lnfix index))))

  ///

  (defret type-var-atom-of-type-var-atom-with-index
    (equal (type-var-kind var) :atom))

  (defrule type-var-atom-with-index-injective
    (equal (equal (type-var-atom-with-index prefix index1)
                  (type-var-atom-with-index prefix index2))
           (equal (nfix index1)
                  (nfix index2)))
    :enable string-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-vars-atom-with-index-below ((prefix stringp) (index natp))
  :returns (vars type-var-setp)
  :short "Generate the set of atom type variables
          for all the numeric indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to remove, from the set of variables to be avoided,
     all the failed attempts at generating a fresh variable.")
   (xdoc::p
    "Membership and subset reduce to index comparison;
     the injectivity of @(tsee type-var-atom-with-index) is needed here.
     This function is also injective."))
  (b* (((when (zp index)) nil)
       (index (1- index)))
    (set::insert (type-var-atom-with-index prefix index)
                 (type-vars-atom-with-index-below prefix index)))
  :verify-guards :after-returns
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defrule type-var-atom-with-index-in-set-below
    (equal (set::in (type-var-atom-with-index prefix index1)
                    (type-vars-atom-with-index-below prefix index2))
           (< (nfix index1)
              (nfix index2)))
    :induct t
    :enable nfix)

  (defrule type-vars-atom-with-index-below-subset
    (equal (set::subset (type-vars-atom-with-index-below prefix index1)
                        (type-vars-atom-with-index-below prefix index2))
           (<= (nfix index1) (nfix index2)))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defrule if-part
       (implies (<= (nfix index1) (nfix index2))
                (set::subset (type-vars-atom-with-index-below prefix index1)
                             (type-vars-atom-with-index-below prefix index2)))
       :induct t)
     (defrule only-if-part
       (implies (set::subset (type-vars-atom-with-index-below prefix index1)
                             (type-vars-atom-with-index-below prefix index2))
                (<= (nfix index1) (nfix index2)))
       :induct t
       :enable nfix)))

  (defrule type-vars-atom-with-index-below-injective
    (implies (equal (type-vars-atom-with-index-below prefix index1)
                    (type-vars-atom-with-index-below prefix index2))
             (equal (nfix index1) (nfix index2)))
    :enable set::double-containment-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-type-vars-atom-below-index ((prefix stringp)
                                           (index natp)
                                           (vars type-var-setp))
  :returns (new-vars type-var-setp)
  :short "Remove, from a set of type variables,
          all the atom type variables with indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the termination argument for generating fresh variables,
     the set @('vars') is the one to be avoided.
     So when we remove the variables below the index,
     we remove all the variables attempted so far."))
  (set::difference (type-var-set-fix vars)
                   (type-vars-atom-with-index-below prefix index))

  ///

  (defrule type-var-atom-with-index-in-remove-type-vars-atoms-below-index
    (equal (set::in (type-var-atom-with-index prefix index1)
                    (remove-type-vars-atom-below-index prefix index2 vars))
           (and (set::in (type-var-atom-with-index prefix index1)
                         (type-var-set-fix vars))
                (>= (nfix index1) (nfix index2)))))

  (defrule remove-type-vars-atom-below-index-subset-when-index-leq
    (implies (>= (nfix index1) (nfix index2))
             (set::subset
              (remove-type-vars-atom-below-index prefix index1 vars)
              (remove-type-vars-atom-below-index prefix index2 vars)))
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-atom-type-var ((prefix stringp) (used type-var-setp))
  :returns (var type-varp)
  :short "Generate a fresh atom type variable,
          i.e. one not in the set of already used type variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the approach in @(see fresh-variables).
     The termination lemma relies on the set theorem explained earlier."))
  (fresh-atom-type-var-loop prefix 0 used)

  :prepwork
  ((define fresh-atom-type-var-loop ((prefix stringp)
                                     (index natp)
                                     (used type-var-setp))
     :returns (var type-varp)
     :parents nil
     (b* ((var (type-var-atom-with-index prefix index)))
       (if (set::in var (type-var-set-fix used))
           (fresh-atom-type-var-loop prefix (1+ (lnfix index)) used)
         var))
     :measure (set::cardinality
               (remove-type-vars-atom-below-index prefix index used))
     :prepwork
     ((defrulel termination-lemma
        (implies (set::in (type-var-atom-with-index prefix index)
                          (type-var-set-fix vars))
                 (< (set::cardinality
                     (remove-type-vars-atom-below-index prefix
                                                        (1+ (nfix index))
                                                        vars))
                    (set::cardinality
                     (remove-type-vars-atom-below-index prefix
                                                        index
                                                        vars))))
        :use (:instance
              cardinality-lt-when-subset-and-not-member
              (x (remove-type-vars-atom-below-index prefix
                                                    (1+ (nfix index))
                                                    vars))
              (y (remove-type-vars-atom-below-index prefix
                                                    index
                                                    vars))
              (a (type-var-atom-with-index prefix index)))))

     ///

     (defret type-var-atom-of-fresh-atom-type-var-loop
       (equal (type-var-kind var) :atom)
       :hints (("Goal" :induct t)))

     (defret fresh-atom-type-var-loop-is-fresh
       (not (set::in var (type-var-set-fix used)))
       :hints (("Goal" :induct t)))))

  ///

  (defret type-var-atom-of-fresh-atom-type-var
    (equal (type-var-kind var) :atom))

  (defret fresh-atom-type-var-is-fresh
    (not (set::in var (type-var-set-fix used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-var-array-with-index ((prefix stringp) (index natp))
  :returns (var type-varp)
  :short "Generate an array type variable from a numeric index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In concrete syntax,
     the variable would have the form @('*<p><i>'),
     where @('<p>') is the prefix and @('<i>') is the index.
     If the prefix is a legal Remora identifier,
     so is the generated variable's name.
     A key property is that it is an injective mapping:
     different indices yield different variables."))
  (type-var-array (str::cat prefix (str::nat-to-dec-string (lnfix index))))

  ///

  (defret type-var-array-of-type-var-array-with-index
    (equal (type-var-kind var) :array))

  (defrule type-var-array-with-index-injective
    (equal (equal (type-var-array-with-index prefix index1)
                  (type-var-array-with-index prefix index2))
           (equal (nfix index1)
                  (nfix index2)))
    :enable string-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-vars-array-with-index-below ((prefix stringp) (index natp))
  :returns (vars type-var-setp)
  :short "Generate the set of array type variables
          for all the numeric indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to remove, from the set of variables to be avoided,
     all the failed attempts at generating a fresh variable.")
   (xdoc::p
    "Membership and subset reduce to index comparison;
     the injectivity of @(tsee type-var-array-with-index) is needed here.
     This function is also injective."))
  (b* (((when (zp index)) nil)
       (index (1- index)))
    (set::insert (type-var-array-with-index prefix index)
                 (type-vars-array-with-index-below prefix index)))
  :verify-guards :after-returns
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defrule type-var-array-with-index-in-set-below
    (equal (set::in (type-var-array-with-index prefix index1)
                    (type-vars-array-with-index-below prefix index2))
           (< (nfix index1)
              (nfix index2)))
    :induct t
    :enable nfix)

  (defrule type-vars-array-with-index-below-subset
    (equal (set::subset (type-vars-array-with-index-below prefix index1)
                        (type-vars-array-with-index-below prefix index2))
           (<= (nfix index1) (nfix index2)))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defrule if-part
       (implies (<= (nfix index1) (nfix index2))
                (set::subset (type-vars-array-with-index-below prefix index1)
                             (type-vars-array-with-index-below prefix index2)))
       :induct t)
     (defrule only-if-part
       (implies (set::subset (type-vars-array-with-index-below prefix index1)
                             (type-vars-array-with-index-below prefix index2))
                (<= (nfix index1) (nfix index2)))
       :induct t
       :enable nfix)))

  (defrule type-vars-array-with-index-below-injective
    (implies (equal (type-vars-array-with-index-below prefix index1)
                    (type-vars-array-with-index-below prefix index2))
             (equal (nfix index1) (nfix index2)))
    :enable set::double-containment-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-type-vars-array-below-index ((prefix stringp)
                                            (index natp)
                                            (vars type-var-setp))
  :returns (new-vars type-var-setp)
  :short "Remove, from a set of type variables,
          all the array type variables with indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the termination argument for generating fresh variables,
     the set @('vars') is the one to be avoided.
     So when we remove the variables below the index,
     we remove all the variables attempted so far."))
  (set::difference (type-var-set-fix vars)
                   (type-vars-array-with-index-below prefix index))

  ///

  (defrule type-var-array-with-index-in-remove-type-vars-arrays-below-index
    (equal (set::in (type-var-array-with-index prefix index1)
                    (remove-type-vars-array-below-index prefix index2 vars))
           (and (set::in (type-var-array-with-index prefix index1)
                         (type-var-set-fix vars))
                (>= (nfix index1) (nfix index2)))))

  (defrule remove-type-vars-array-below-index-subset-when-index-leq
    (implies (>= (nfix index1) (nfix index2))
             (set::subset
              (remove-type-vars-array-below-index prefix index1 vars)
              (remove-type-vars-array-below-index prefix index2 vars)))
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-array-type-var ((prefix stringp) (used type-var-setp))
  :returns (var type-varp)
  :short "Generate a fresh array type variable,
          i.e. one not in the set of already used type variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the approach in @(see fresh-variables).
     The termination lemma relies on the set theorem explained earlier."))
  (fresh-array-type-var-loop prefix 0 used)

  :prepwork
  ((define fresh-array-type-var-loop ((prefix stringp)
                                      (index natp)
                                      (used type-var-setp))
     :returns (var type-varp)
     :parents nil
     (b* ((var (type-var-array-with-index prefix index)))
       (if (set::in var (type-var-set-fix used))
           (fresh-array-type-var-loop prefix (1+ (lnfix index)) used)
         var))
     :measure (set::cardinality
               (remove-type-vars-array-below-index prefix index used))
     :prepwork
     ((defrulel termination-lemma
        (implies (set::in (type-var-array-with-index prefix index)
                          (type-var-set-fix vars))
                 (< (set::cardinality
                     (remove-type-vars-array-below-index prefix
                                                         (1+ (nfix index))
                                                         vars))
                    (set::cardinality
                     (remove-type-vars-array-below-index prefix
                                                         index
                                                         vars))))
        :use (:instance
              cardinality-lt-when-subset-and-not-member
              (x (remove-type-vars-array-below-index prefix
                                                     (1+ (nfix index))
                                                     vars))
              (y (remove-type-vars-array-below-index prefix
                                                     index
                                                     vars))
              (a (type-var-array-with-index prefix index)))))

     ///

     (defret type-var-array-of-fresh-array-type-var-loop
       (equal (type-var-kind var) :array)
       :hints (("Goal" :induct t)))

     (defret fresh-array-type-var-loop-is-fresh
       (not (set::in var (type-var-set-fix used)))
       :hints (("Goal" :induct t)))))

  ///

  (defret type-var-array-of-fresh-array-type-var
    (equal (type-var-kind var) :array))

  (defret fresh-array-type-var-is-fresh
    (not (set::in var (type-var-set-fix used)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-var-with-index ((prefix stringp) (index natp))
  :returns (var stringp)
  :short "Generate an expression variable
          from a prefix and a numeric index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In concrete syntax,
     the variable would have the form @('<p><i>'),
     where @('<p>') is the prefix and @('<i>') is the index.
     If the prefix is a legal Remora identifier,
     so is the generated variable's name.
     A key property is that it is an injective mapping given a prefix:
     different indices yield different variables."))
  (str::cat prefix (str::nat-to-dec-string (lnfix index)))

  ///

  (defrule expr-var-with-index-injective
    (equal (equal (expr-var-with-index prefix index1)
                  (expr-var-with-index prefix index2))
           (equal (nfix index1)
                  (nfix index2)))
    :enable string-append))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-vars-with-index-below ((prefix stringp) (index natp))
  :returns (vars string-setp)
  :short "Generate the set of expression variables
          with a given prefix for all the numeric indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to remove, from the set of variables to be avoided,
     all the failed attempts at generating a fresh variable.")
   (xdoc::p
    "Membership and subset reduce to index comparison;
     the injectivity of @(tsee expr-var-with-index) is needed here.
     This function is also injective."))
  (b* (((when (zp index)) nil)
       (index (1- index)))
    (set::insert (expr-var-with-index prefix index)
                 (expr-vars-with-index-below prefix index)))
  :verify-guards :after-returns
  :prepwork ((local (in-theory (enable nfix))))

  ///

  (defrule expr-var-with-index-in-set-below
    (equal (set::in (expr-var-with-index prefix index1)
                    (expr-vars-with-index-below prefix index2))
           (< (nfix index1)
              (nfix index2)))
    :induct t
    :enable nfix)

  (defrule expr-vars-with-index-below-subset
    (equal (set::subset (expr-vars-with-index-below prefix index1)
                        (expr-vars-with-index-below prefix index2))
           (<= (nfix index1) (nfix index2)))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defrule if-part
       (implies (<= (nfix index1) (nfix index2))
                (set::subset (expr-vars-with-index-below prefix index1)
                             (expr-vars-with-index-below prefix index2)))
       :induct t)
     (defrule only-if-part
       (implies (set::subset (expr-vars-with-index-below prefix index1)
                             (expr-vars-with-index-below prefix index2))
                (<= (nfix index1) (nfix index2)))
       :induct t
       :enable nfix)))

  (defrule expr-vars-with-index-below-injective
    (implies (equal (expr-vars-with-index-below prefix index1)
                    (expr-vars-with-index-below prefix index2))
             (equal (nfix index1) (nfix index2)))
    :enable set::double-containment-no-backchain-limit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define remove-expr-vars-below-index ((prefix stringp)
                                      (index natp)
                                      (vars string-setp))
  :returns (new-vars string-setp)
  :short "Remove, from a set of expression variables,
          all the expression variables
          with a given prefix and with indices below a given index."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the termination argument for generating fresh variables,
     the set @('vars') is the one to be avoided.
     So when we remove the variables below the index,
     we remove all the variables attempted so far."))
  (set::difference (string-sfix vars)
                   (expr-vars-with-index-below prefix index))

  ///

  (defrule expr-var-with-index-in-remove-expr-vars-below-index
    (equal (set::in (expr-var-with-index prefix index1)
                    (remove-expr-vars-below-index prefix index2 vars))
           (and (set::in (expr-var-with-index prefix index1)
                         (string-sfix vars))
                (>= (nfix index1) (nfix index2)))))

  (defrule remove-expr-vars-below-index-subset-when-index-leq
    (implies (>= (nfix index1) (nfix index2))
             (set::subset
              (remove-expr-vars-below-index prefix index1 vars)
              (remove-expr-vars-below-index prefix index2 vars)))
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fresh-expr-var ((prefix stringp) (used string-setp))
  :returns (var stringp)
  :short "Generate a fresh expression variable,
          i.e. one not in the set of already used expression variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the approach in @(see fresh-variables).
     The termination lemma relies on the set theorem explained earlier."))
  (fresh-expr-var-loop prefix 0 used)

  :prepwork
  ((define fresh-expr-var-loop ((prefix stringp)
                                (index natp)
                                (used string-setp))
     :returns (var stringp)
     :parents nil
     (b* ((var (expr-var-with-index prefix index)))
       (if (set::in var (string-sfix used))
           (fresh-expr-var-loop prefix (1+ (lnfix index)) used)
         var))
     :measure (set::cardinality
               (remove-expr-vars-below-index prefix index used))
     :prepwork
     ((defrulel termination-lemma
        (implies (set::in (expr-var-with-index prefix index)
                          (string-sfix vars))
                 (< (set::cardinality
                     (remove-expr-vars-below-index prefix
                                                   (1+ (nfix index))
                                                   vars))
                    (set::cardinality
                     (remove-expr-vars-below-index prefix
                                                   index
                                                   vars))))
        :use (:instance
              cardinality-lt-when-subset-and-not-member
              (x (remove-expr-vars-below-index prefix
                                               (1+ (nfix index))
                                               vars))
              (y (remove-expr-vars-below-index prefix
                                               index
                                               vars))
              (a (expr-var-with-index prefix index)))))

     ///

     (defret fresh-expr-var-loop-is-fresh
       (not (set::in var (string-sfix used)))
       :hints (("Goal" :induct t)))))

  ///

  (defret fresh-expr-var-is-fresh
    (not (set::in var (string-sfix used)))))
