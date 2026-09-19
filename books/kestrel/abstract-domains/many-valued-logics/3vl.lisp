; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 3vl
  :parents (many-valued-logics)
  :short "A three-valued logic."
  :long
  (xdoc::topstring
   (xdoc::p
    "This logic extends booleans and boolean operations with a third value,
     @(':unknown').
     As the symbol name suggests,
     this value indicates the result may be @('nil') or @('t'),
     but we are uncertain which.
     You might also read it as ``maybe''.")
   (xdoc::p
    "When applied to boolean values,
     the three-valued logic operators behave
     exactly like their traditional boolean counterparts.")
   (xdoc::p
    "Two partial orders are defined on this logic.
     The information order @(tsee 3info<), also known as the knowledge order,
     relates more specific values to less specific values.
     That is, we have
     just @('(3info< nil :unknown)') and @('(3info< t :unknown)').
     Under this order, the logic forms a join-semilattice,
     where @(tsee 3join) is the join.")
   (xdoc::p
    "(There is no meet under @(tsee 3info<),
     because there is no lower bound for @('nil') and @('t').
     If we wished to add a meet, we would need to introduce a bottom element,
     which we might call ``contradiction''.
     The interpretation of this element is more complicated &mdash;
     it would indicate that the value is
     <em>both</em> @('nil') <em>and</em> @('t').
     This would make a sensible four-valued logic,
     which we may add at some point in the future.
     For now, we avoid the complication.)")
   (xdoc::p
    "The truth order @(tsee 3truth<) instead relates
     ``falser'' values to ``truer' values:
     @('(3truth< nil :unknown)'), @('(3truth< :unknown t)'),
     and so @('(3truth< nil t)').
     Under this order, the logic forms a lattice, where
     @(tsee 3and) is the meet and @(tsee 3or) is the join.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3p (x)
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Recognizer for three-value logic values."
  :long
  (xdoc::topstring-p
   "Checks that the recognized value is @('nil'), @('t'), or @(':unknown').")
  (or (eq x t)
      (eq x nil)
      (eq x :unknown))
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3p-type-prescription
  (booleanp (3p x))
  :rule-classes ((:type-prescription :typed-term (3p x))))

(defrule 3p-compound-recognizer
  (if (3p x)
      (symbolp x)
    (and (not (equal x t))
         (not (equal x nil))))
  :rule-classes :compound-recognizer
  :enable 3p)

(defrule 3p-when-booleanp
  (implies (booleanp x)
           (3p x))
  :enable 3p)

(defruled booleanp-when-3p
  (implies (3p x)
           (equal (booleanp x)
                  (not (equal x :unknown))))
  :enable 3p)

(defrule booleanp-when-3p-cheap
  (implies (3p x)
           (equal (booleanp x)
                  (not (equal x :unknown))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by booleanp-when-3p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3fix ((x 3p))
  :returns (x$ 3p)
  :parents (3vl)
  :short "A fixing function for @(see 3p)s."
  :long
  (xdoc::topstring-p
   "If the argument is not a @(see 3p), we default to @(':unknown').")
  (mbe :logic (if (3p x)
                  x
                :unknown)
       :exec x)
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3fix-type-prescription
  (3p (3fix x))
  :rule-classes ((:type-prescription :typed-term (3fix x))))

(defrule 3fix-when-3p
  (implies (3p x)
           (equal (3fix x)
                  x))
  :enable 3fix)

(defruled 3fix-when-not-3p
  (implies (not (3p x))
           (equal (3fix x)
                  :unknown))
  :enable 3fix)

(defrule 3fix-when-not-3p-cheap
  (implies (not (3p x))
           (equal (3fix x)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3fix-when-not-3p)

(defrule booleanp-of-3fix
  (equal (booleanp (3fix x))
         (booleanp x))
  :enable 3fix)

(defruled 3fix-when-not-booleanp
  (implies (not (booleanp x))
           (equal (3fix x)
                  :unknown))
  :enable 3fix)

(defrule 3fix-when-not-booleanp-cheap
  (implies (not (booleanp x))
           (equal (3fix x)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3fix-when-not-booleanp)

(defrule 3fix-under-iff
  (iff (3fix x)
       (double-rewrite x))
  :enable 3fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3equiv
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Equivalence of @(see 3p)s."
  :long
  (xdoc::topstring-p
   "This is a typical equality of fixers.
    Note that this is <em>not</em> the same as @(tsee 3iff).")
  (eq (3fix x)
      (3fix y))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3equiv-type-prescription
  (booleanp (3equiv x y))
  :rule-classes ((:type-prescription :typed-term (3equiv x y))))

(defequiv 3equiv
  :hints (("Goal" :in-theory (enable 3equiv))))

(defrule 3fix-when-3equiv-congruence
  (implies (3equiv tri0 tri1)
           (equal (3fix tri0)
                  (3fix tri1)))
  :rule-classes :congruence
  :enable 3equiv)

(defrule 3fix-under-3equiv
  (3equiv (3fix x)
          x)
  :enable 3equiv)

(defrule iff-when-3equiv
  (implies (3equiv x y)
           (iff x y))
  :rule-classes :refinement
  :enable 3equiv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3info<
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare specificity of @(see 3p)s."
  :long
  (xdoc::topstring-p
   "This forms a join-semilattice on @(see 3p)s.
    See @(see 3vl) for more detail.")
  (let ((x (3fix x))
        (y (3fix y)))
    (and (not (eq x :unknown))
         (eq y :unknown)))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3info<-type-prescription
  (booleanp (3info< x y))
  :rule-classes ((:type-prescription :typed-term (3info< x y))))

(defrule 3info<-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3info< x0 y)
                  (3info< x1 y)))
  :rule-classes :congruence
  :enable 3info<)

(defrule 3info<-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3info< x y0)
                  (3info< x y1)))
  :rule-classes :congruence
  :enable 3info<)

(defruled 3info<-when-booleanp-of-arg1
  (implies (booleanp x)
           (equal (3info< x y)
                  (not (booleanp y))))
  :enable 3info<)

(defrule 3info<-when-booleanp-of-arg1-cheap
  (implies (booleanp x)
           (equal (3info< x y)
                  (not (booleanp y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<-when-booleanp-of-arg1)

(defruled 3info<-when-booleanp-of-arg2
  (implies (booleanp y)
           (not (3info< x y)))
  :enable 3info<)

(defrule 3info<-when-booleanp-of-arg2-cheap
  (implies (booleanp y)
           (not (3info< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<-when-booleanp-of-arg2)

(defruled 3info<-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (not (3info< x y)))
  :enable 3info<)

(defrule 3info<-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (not (3info< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<-when-not-booleanp-of-arg1)

(defruled 3info<-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (equal (3info< x y)
                  (booleanp x)))
  :enable 3info<)

(defrule 3info<-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (equal (3info< x y)
                  (booleanp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<-when-not-booleanp-of-arg2)

(defrule irreflexivity-of-3info<
  (not (3info< x x))
  :enable 3info<)

(defruled asymmetry-of-3info<
  (implies (3info< x y)
           (not (3info< y x)))
  :enable 3info<)

(defrule asymmetry-of-3info<-forward-chaining
  (implies (3info< x y)
           (not (3info< y x)))
  :rule-classes :forward-chaining
  :by asymmetry-of-3info<)

(defruled 3fix-when-3info<
  (implies (3info< x y)
           (equal (3fix y)
                  :unknown))
  :enable 3info<)

(defrule arg2-under-3equiv-when-3info<-forward-chaining
  (implies (3info< x y)
           (3equiv y :unknown))
  :rule-classes :forward-chaining
  :enable (3info<
           3equiv))

;; 3info< is technically transitive, but it isn't a useful rule, since it is
;; trivialized by arg2-under-3equiv-when-3info<-forward-chaining.
(defruled transitivity-of-3info<
  (implies (and (3info< x y)
                (3info< y z))
           (3info< x z)))

(defruled booleanp-when-3info<
  (implies (and (3equiv x$ (double-rewrite x))
                (3info< x y))
           (booleanp x))
  :enable 3info<)

(defrule booleanp-when-3info<-forward-chaining
  (implies (3info< x y)
           (booleanp x))
  :rule-classes :forward-chaining
  :use booleanp-when-3info<)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3info<=
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare weak specificity of @(see 3p)s."
  :long
  (xdoc::topstring-p
   "Recognizes values that are either @(tsee 3info<) or @(tsee 3equiv).")
  (mbe :logic (or (equal (3fix x)
                         (3fix y))
                  (3info< x y))
       :exec (or (eq x y)
                 (eq y :unknown)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable 3info<)))
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3info<=-type-prescription
  (booleanp (3info<= x y))
  :rule-classes ((:type-prescription :typed-term (3info<= x y))))

(defrule 3info<=-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3info<= x0 y)
                  (3info<= x1 y)))
  :rule-classes :congruence
  :enable 3info<=)

(defrule 3info<=-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3info<= x y0)
                  (3info<= x y1)))
  :rule-classes :congruence
  :enable 3info<=)

(defruled 3info<=-when-booleanp-of-arg2
  (implies (booleanp y)
           (equal (3info<= x y)
                  (equal x y)))
  :enable 3info<=)

(defrule 3info<=-when-booleanp-of-arg2-cheap
  (implies (booleanp y)
           (equal (3info<= x y)
                  (equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<=-when-booleanp-of-arg2)

(defruled 3info<=-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (equal (3info<= x y)
                  (not (booleanp y))))
  :enable 3info<=)

(defrule 3info<=-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (equal (3info<= x y)
                  (not (booleanp y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<=-when-not-booleanp-of-arg1)

(defruled 3info<=-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (3info<= x y))
  :enable 3info<=)

(defrule 3info<=-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (3info<= x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3info<=-when-not-booleanp-of-arg2)

(defruled 3info<=-of-nil
  (equal (3info<= nil y)
         (not (equal y t)))
  :enable (3info<=
           booleanp))

(defruled 3info<=-of-t
  (equal (3info<= t y)
         (and (double-rewrite y) t))
  :enable 3info<=)

(defrule reflexivity-of-3info<=
  (3info<= x x)
  :enable 3info<=)

(defruled antisymmetry-of-3info<=-weak
  (implies (and (3info<= x y)
                (3info<= y x))
           (3equiv x y))
  :enable (3info<=
           3equiv))

(defruled antisymmetry-of-3info<=
  (equal (and (3info<= x y)
              (3info<= y x))
         (3equiv x y))
  :use antisymmetry-of-3info<=-weak)

(defrule antisymmetry-of-3info<=-forward-chaining
  (implies (and (3info<= x y)
                (3info<= y x))
           (3equiv x y))
  :rule-classes :forward-chaining
  :by antisymmetry-of-3info<=-weak)

(defrule transitivity-of-3info<=
  (implies (and (3info<= x y)
                (3info<= y z))
           (3info<= x z))
  :enable (3info<=
           3fix))

(defrule 3info<=-when-3info<
  (implies (3info< x y)
           (3info<= x y))
  :enable 3info<=)

(defruled 3info<-when-not-3info<=
  (implies (not (3info<= x y))
           (not (3info< x y))))

(defrule 3info<-when-not-3info<=-forward-chaining
  (implies (not (3info<= x y))
           (not (3info< x y)))
  :rule-classes :forward-chaining
  :by 3info<-when-not-3info<=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3join
  :parents (3vl)
  :short "The join on the @(tsee 3info<) semilattice."

  (define binary-3join$inline
    ((x 3p)
     (y 3p))
    :returns (join 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (if (eq x y)
          x
        :unknown))
    :type-prescription :none
    ///

    (defmacro 3join (x &rest rest)
      (if (endp rest)
          (cons '3fix (list x))
        (xxxjoin 'binary-3join$inline (cons x rest))))

    (add-macro-fn 3join binary-3join$inline t)))

;;;;;;;;;;;;;;;;;;;;

(defrule 3join-type-prescription
  (3p (3join x y))
  :rule-classes ((:type-prescription :typed-term (3join x y))))

(defrule 3join-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3join x0 y)
                  (3join x1 y)))
  :rule-classes :congruence
  :enable 3join)

(defrule 3join-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3join x y0)
                  (3join x y1)))
  :rule-classes :congruence
  :enable 3join)

(defrule associativity-of-3join
  (equal (3join (3join x y) z)
         (3join x y z))
  :enable 3join)

(defrule commutativity-of-3join
  (equal (3join y x)
         (3join x y))
  :enable 3join)

(defrule commutativity-2-of-3join
  (equal (3join y x z)
         (3join x y z))
  :enable 3join)

(defrule idempotence-of-3join
  (equal (3join x x)
         (3fix x))
  :enable 3join)

(defrule 3join-contraction
  (equal (3join x x y)
         (3join x y))
  :enable 3join)

(defruled 3join-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (equal (3join x y)
                  :unknown))
  :enable 3join)

(defrule 3join-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (equal (3join x y)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3join-when-not-booleanp-of-arg1)

(defruled 3join-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (equal (3join x y)
                  :unknown))
  :enable 3join)

(defrule 3join-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (equal (3join x y)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3join-when-not-booleanp-of-arg2)

(defruled monotonicity-of-3join-left
  (implies (and (3info<= x0 x1))
           (3info<= (3join x0 y)
                (3join x1 y)))
  :enable 3join)

(defruled monotonicity-of-3join-right
  (implies (and (3info<= y0 y1))
           (3info<= (3join x y0)
                (3join x y1)))
  :enable 3join)

(defrule monotonicity-of-3join
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3join x0 y0)
                (3join x1 y1)))
  :enable 3join)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3not ((x 3p))
  :returns (negation 3p)
  :parents (3vl)
  :short "Extension of @(see not) to @(see 3vl)."
  (let ((x (3fix x)))
    (if (eq x :unknown)
        :unknown
      (not x)))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3not-type-prescription
  (3p (3not x))
  :rule-classes ((:type-prescription :typed-term (3not x))))

(defrule 3not-when-3equiv-congruence
  (implies (3equiv x0 x1)
           (equal (3not x0)
                  (3not x1)))
  :rule-classes :congruence
  :enable 3not)

(defrule booleanp-of-3not
  (equal (booleanp (3not x))
         (booleanp x))
  :enable (3not
           3fix))

(defrule 3not-involution
  (equal (3not (3not x))
         (3fix x))
  :enable (3not
           3fix
           3p))

(defruled monotonicity-of-3not-weak
  (implies (3info<= x0 x1)
           (3info<= (3not x0)
                (3not x1)))
  :enable (3not
           3info<=
           3info<))

(defrule monotonicity-of-3not
  (equal (3info<= (3not x0)
              (3not x1))
         (3info<= x0 x1))
  :enable (3not
           3fix
           3p))

(defruled 3not-when-booleanp
  (implies (booleanp x)
           (equal (3not x)
                  (not (double-rewrite x))))
  :enable 3not)

(defrule 3not-when-booleanp-cheap
  (implies (booleanp x)
           (equal (3not x)
                  (not (double-rewrite x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3not-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3and
  :parents (3vl)
  :short "Extension of @(see and) to @(see 3vl)."

  (define binary-3and$inline
    ((x 3p)
     (y 3p))
    :returns (conjunction 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (cond ((or (not x) (not y)) nil)
            ((or (eq x :unknown) (eq y :unknown)) :unknown)
            (t t)))
    :type-prescription :none
    ///

    (defmacro 3and (&rest rest)
      (if (endp rest)
          t
        (if (rest rest)
            (xxxjoin 'binary-3and$inline rest)
          (cons '3fix
                (list (first rest))))))

    (add-macro-fn 3and binary-3and$inline t)))

;;;;;;;;;;;;;;;;;;;;

(defrule 3and-type-prescription
  (3p (3and x y))
  :rule-classes ((:type-prescription :typed-term (3and x y))))

(defrule 3and-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3and x0 y)
                  (3and x1 y)))
  :rule-classes :congruence
  :enable 3and)

(defrule 3and-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3and x y0)
                  (3and x y1)))
  :rule-classes :congruence
  :enable 3and)

(defrule booleanp-of-3and
  (equal (booleanp (3and x y))
         (or (not (double-rewrite x))
             (not (double-rewrite y))
             (and (equal x t)
                  (equal y t))))
  :enable (3and
           3fix
           3p))

(defrule associativity-of-3and
  (equal (3and (3and x y) z)
         (3and x y z))
  :enable 3and)

(defrule commutativity-of-3and
  (equal (3and y x)
         (3and x y))
  :enable 3and)

(defrule commutativity-2-of-3and
  (equal (3and y x z)
         (3and x y z))
  :enable 3and)

(defrule 3and-of-nil
  (equal (3and nil y)
         nil)
  :enable 3and)

(defrule 3and-of-arg1-and-nil
  (equal (3and x nil)
         nil)
  :enable 3and)

(defrule 3and-of-t
  (equal (3and t y)
         (3fix y))
  :enable (3and
           3fix
           3p))

(defrule 3and-of-arg1-and-t
  (equal (3and x t)
         (3fix x)))

(defrule idempotence-of-3and
  (equal (3and x x)
         (3fix x))
  :enable (3and
           3fix
           3p))

(defrule 3and-contraction
  (equal (3and x x y)
         (3and x y))
  :enable 3and)

(defrule monotonicity-of-3and
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3and x0 y0)
                (3and x1 y1)))
  :enable (3and
           3info<=
           3info<))

(defruled 3and-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3and x y)
                  (and (double-rewrite x) y)))
  :enable 3and)

(defrule 3and-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3and x y)
                  (and (double-rewrite x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3and-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3or
  :parents (3vl)
  :short "Extension of @(see or) to @(see 3vl)."

  (define binary-3or$inline
    ((x 3p)
     (y 3p))
    :returns (disjunction 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (cond ((or (eq x t) (eq y t)) t)
            ((or (eq x :unknown) (eq y :unknown)) :unknown)
            (t nil)))
    :type-prescription :none
    ///

    (defmacro 3or (&rest rest)
      (if (endp rest)
          nil
        (if (rest rest)
            (xxxjoin 'binary-3or$inline rest)
          (cons '3fix
                (list (first rest))))))

    (add-macro-fn 3or binary-3or$inline t)))

;;;;;;;;;;;;;;;;;;;;

(defrule 3or-type-prescription
  (3p (3or x y))
  :rule-classes ((:type-prescription :typed-term (3or x y))))

(defrule 3or-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3or x0 y)
                  (3or x1 y)))
  :rule-classes :congruence
  :enable 3or)

(defrule 3or-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3or x y0)
                  (3or x y1)))
  :rule-classes :congruence
  :enable 3or)

(defrule booleanp-of-3or
  (equal (booleanp (3or x y))
         (or (equal x t)
             (equal y t)
             (and (equal x nil)
                  (equal y nil))))
  :enable (3or
           3fix
           3p))

(defrule associativity-of-3or
  (equal (3or (3or x y) z)
         (3or x y z))
  :enable 3or)

(defrule commutativity-of-3or
  (equal (3or y x)
         (3or x y))
  :enable 3or)

(defrule commutativity-2-of-3or
  (equal (3or y x z)
         (3or x y z))
  :enable 3or)

(defrule 3or-of-nil
  (equal (3or nil y)
         (3fix y))
  :enable (3or
           3fix
           3p))

(defrule 3or-of-arg1-or-nil
  (equal (3or x nil)
         (3fix x))
  :enable (3or
           3fix
           3p))

(defrule 3or-of-t
  (equal (3or t y)
         t)
  :enable 3or)

(defrule 3or-of-arg1-or-t
  (equal (3or x t)
         t))

(defrule idempotence-of-3or
  (equal (3or x x)
         (3fix x))
  :enable (3or
           3fix
           3p))

(defrule 3or-contraction
  (equal (3or x x y)
         (3or x y))
  :enable 3or)

(defrule monotonicity-of-3or
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3or x0 y0)
                (3or x1 y1)))
  :enable (3or
           3info<=
           3info<))

(defruled 3or-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3or x y)
                  (or (double-rewrite x) y)))
  :enable 3or)

(defrule 3or-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3or x y)
                  (or (double-rewrite x) y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3or-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3xor
  :parents (3vl)
  :short "Extension of @(see xor) to @(see 3vl)."

  (define binary-3xor$inline
    ((x 3p)
     (y 3p))
    :returns (xjunction 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (if (or (eq x :unknown)
              (eq y :unknown))
          :unknown
        (not (eq x y))))
    :type-prescription :none
    ///

    (defmacro 3xor (&rest rest)
      (if (endp rest)
          nil
        (if (rest rest)
            (xxxjoin 'binary-3xor$inline rest)
          (cons '3fix
                (list (first rest))))))

    (add-macro-fn 3xor binary-3xor$inline t)))

;;;;;;;;;;;;;;;;;;;;

(defrule 3xor-type-prescription
  (3p (3xor x y))
  :rule-classes ((:type-prescription :typed-term (3xor x y))))

(defrule 3xor-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3xor x0 y)
                  (3xor x1 y)))
  :rule-classes :congruence
  :enable 3xor)

(defrule 3xor-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3xor x y0)
                  (3xor x y1)))
  :rule-classes :congruence
  :enable 3xor)

(defrule booleanp-of-3xor
  (equal (booleanp (3xor x y))
         (and (booleanp x)
              (booleanp y)))
  :enable 3xor)

(defrule associativity-of-3xor
  (equal (3xor (3xor x y) z)
         (3xor x y z))
  :enable (3xor
           3fix
           3p))

(defrule commutativity-of-3xor
  (equal (3xor y x)
         (3xor x y))
  :enable 3xor)

(defrule commutativity-2-of-3xor
  (equal (3xor y x z)
         (3xor x y z))
  :enable (3xor
           3fix
           3p))

(defrule 3xor-of-nil
  (equal (3xor nil y)
         (3fix y))
  :enable (3xor
           3fix
           3p))

(defrule 3xor-of-arg1-and-nil
  (equal (3xor x nil)
         (3fix x))
  :enable (3xor
           3fix
           3p))

(defrule 3xor-of-t
  (equal (3xor t y)
         (3not y))
  :enable (3xor
           3not
           3fix
           3p))

(defrule 3xor-of-arg1-or-t
  (equal (3xor x t)
         (3not x)))

(defrule monotonicity-of-3xor
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3xor x0 y0)
                (3xor x1 y1)))
  :enable (3xor
           3info<=
           3info<))

(defruled 3xor-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3xor x y)
                  (xor x y)))
  :enable (3xor
           xor))

(defrule 3xor-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3xor x y)
                  (xor x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3xor-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3implies
  ((x 3p)
   (y 3p))
  :returns (conditional 3p)
  :parents (3vl)
  :short "Extension of @(see implies) to @(see 3vl)."
  (let ((x (3fix x))
        (y (3fix y)))
    (or (not x)
        (eq y t)
        (if (eq x t)
            y
          :unknown)))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3implies-type-prescription
  (3p (3implies x y))
  :rule-classes ((:type-prescription :typed-term (3implies x y))))

(defrule 3implies-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3implies x0 y)
                  (3implies x1 y)))
  :rule-classes :congruence
  :enable 3implies)

(defrule 3implies-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3implies x y0)
                  (3implies x y1)))
  :rule-classes :congruence
  :enable 3implies)

(defrule booleanp-of-3implies
  (equal (booleanp (3implies x y))
         (or (not (double-rewrite x))
             (equal y t)
             (and (equal x t)
                  (not (double-rewrite y)))))
  :enable (3implies
           3fix
           3p))

(defrule 3implies-of-nil
  (equal (3implies nil y)
         t)
  :enable 3implies)

(defrule 3implies-of-arg1-and-nil
  (equal (3implies x nil)
         (3not x))
  :enable (3implies
           3not
           3fix
           3p))

(defrule 3implies-of-t
  (equal (3implies t y)
         (3fix y))
  :enable 3implies)

(defrule 3implies-of-arg1-and-t
  (equal (3implies x t)
         t)
  :enable 3implies)

(defrule monotonicity-of-3implies
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3implies x0 y0)
                (3implies x1 y1)))
  :enable (3implies
           3info<=
           3info<))

(defrule 3implies-becomes-3or-definition
  (equal (3implies x y)
         (3or (3not x) y))
  :rule-classes :definition
  :enable (3implies
           3or
           3not
           3fix
           3p))

(defruled 3implies-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3implies x y)
                  (implies (double-rewrite x)
                           (double-rewrite y)))))

(defrule 3implies-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3implies x y)
                  (implies (double-rewrite x)
                           (double-rewrite y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3implies-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3iff
  :parents (3vl)
  :short "Extension of @(see iff) to @(see 3vl)."

  (define binary-3iff$inline
    ((x 3p)
     (y 3p))
    :returns (iff 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (if (or (eq x :unknown)
              (eq y :unknown))
          :unknown
        (eq x y)))
    :type-prescription :none
    ///

    (defmacro 3iff (&rest rest)
      (if (endp rest)
          t
        (if (rest rest)
            (xxxjoin 'binary-3iff$inline rest)
          (cons '3fix
                (list (first rest))))))

    (add-macro-fn 3iff binary-3iff$inline t)))

;;;;;;;;;;;;;;;;;;;;

(defrule 3iff-type-prescription
  (3p (3iff x y))
  :rule-classes ((:type-prescription :typed-term (3iff x y))))

(defrule 3iff-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3iff x0 y)
                  (3iff x1 y)))
  :rule-classes :congruence
  :enable 3iff)

(defrule 3iff-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3iff x y0)
                  (3iff x y1)))
  :rule-classes :congruence
  :enable 3iff)

(defrule booleanp-of-3iff
  (equal (booleanp (3iff x y))
         (and (booleanp x)
              (booleanp y)))
  :enable (3iff
           3fix
           3p))

(defrule associativity-of-3iff
  (equal (3iff (3iff x y) z)
         (3iff x y z))
  :enable (3iff
           3fix
           3p))

(defrule commutativity-of-3iff
  (equal (3iff y x)
         (3iff x y))
  :enable 3iff)

(defrule commutativity-2-of-3iff
  (equal (3iff y x z)
         (3iff x y z))
  :enable (3iff
           3fix
           3p))

(defruled 3iff-of-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (equal (3iff x y)
                  :unknown))
  :enable 3iff)

(defrule 3iff-of-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (equal (3iff x y)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3iff-of-when-not-booleanp-of-arg1)

(defruled 3iff-of-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (equal (3iff x y)
                  :unknown))
  :enable 3iff)

(defrule 3iff-of-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (equal (3iff x y)
                  :unknown))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3iff-of-when-not-booleanp-of-arg2)

(defrule 3iff-of-nil
  (equal (3iff nil y)
         (3not y))
  :enable (3iff
           3not))

(defrule 3iff-of-arg1-or-nil
  (equal (3iff x nil)
         (3not x))
  :enable (3iff
           3not))

(defrule 3iff-of-t
  (equal (3iff t y)
         (3fix y))
  :enable (3iff
           3fix
           3p))

(defrule 3iff-of-arg1-or-t
  (equal (3iff x t)
         (3fix x)))

(defrule monotonicity-of-3iff
  (implies (and (3info<= x0 x1)
                (3info<= y0 y1))
           (3info<= (3iff x0 y0)
                (3iff x1 y1)))
  :enable (3iff
           3info<=
           3info<))

(defruled 3iff-becomes-3not-of-3xor-definition
  (equal (3iff x y)
         (3not (3xor x y)))
  :rule-classes :definition
  :enable (3iff
           3not
           3xor))

(defrule 3iff-becomes-3implies-definition
  (equal (3iff x y)
         (3and (3implies x y)
               (3implies y x)))
  :rule-classes :definition
  :enable (3iff
           3and
           3or
           3not
           3fix
           3p))

(defruled 3iff-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3iff x y)
                  (iff (double-rewrite x)
                       (double-rewrite y)))))

(defrule 3iff-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3iff x y)
                  (iff (double-rewrite x)
                       (double-rewrite y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3iff-when-booleanp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3possibly ((x 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Whether a @(see 3p) may be true."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds of @('t') and @(':unknown'), but not of @('nil').")
   (xdoc::p
    "This is one of the two boolean projections of a @(see 3p),
     the other being @(tsee 3definitely).
     The two are dual under @(tsee 3not)."))
  (not (3equiv x nil))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3possibly-type-prescription
  (booleanp (3possibly x))
  :rule-classes ((:type-prescription :typed-term (3possibly x))))

(defrule 3possibly-when-3equiv-congruence
  (implies (3equiv x0 x1)
           (equal (3possibly x0)
                  (3possibly x1)))
  :rule-classes :congruence
  :enable 3possibly)

(defruled 3possibly-when-booleanp
  (implies (booleanp x)
           (equal (3possibly x)
                  x))
  :enable 3possibly)

(defrule 3possibly-when-booleanp-cheap
  (implies (booleanp x)
           (equal (3possibly x)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3possibly-when-booleanp)

(defruled 3possibly-when-not-booleanp
  (implies (not (booleanp x))
           (3possibly x))
  :enable (3possibly
           3equiv))

(defrule 3possibly-when-not-booleanp-cheap
  (implies (not (booleanp x))
           (3possibly x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3possibly-when-not-booleanp)

(defruled 3fix-when-not-3possibly
  (implies (not (3possibly x))
           (equal (3fix x)
                  nil))
  :enable 3possibly)

(defruled monotonicity-of-3possibly
  (implies (and (3info<= x0 x1)
                (3possibly x0))
           (3possibly x1))
  :enable (3possibly
           3info<=))

(defrule 3possibly-of-3join
  (equal (3possibly (3join x y))
         (or (3possibly x)
             (3possibly y)))
  :enable (3possibly
           3join))

(defrule 3possibly-of-3and
  (equal (3possibly (3and x y))
         (and (3possibly x)
              (3possibly y)))
  :enable (3possibly
           3and))

(defrule 3possibly-of-3or
  (equal (3possibly (3or x y))
         (or (3possibly x)
             (3possibly y)))
  :enable (3possibly
           3or
           3fix
           3p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3definitely ((x 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Whether a @(see 3p) must be true."
  :long
  (xdoc::topstring
   (xdoc::p
    "This holds of @('t') only, and so of neither @('nil') nor @(':unknown').")
   (xdoc::p
    "This is one of the two boolean projections of a @(see 3p),
     the other being @(tsee 3possibly).
     The two are dual under @(tsee 3not)."))
  (3equiv x t)
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3definitely-type-prescription
  (booleanp (3definitely x))
  :rule-classes ((:type-prescription :typed-term (3definitely x))))

(defrule 3definitely-when-3equiv-congruence
  (implies (3equiv x0 x1)
           (equal (3definitely x0)
                  (3definitely x1)))
  :rule-classes :congruence
  :enable 3definitely)

(defruled 3definitely-when-booleanp
  (implies (booleanp x)
           (equal (3definitely x)
                  x))
  :enable (3definitely
           3equiv))

(defrule 3definitely-when-booleanp-cheap
  (implies (booleanp x)
           (equal (3definitely x)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3definitely-when-booleanp)

(defruled 3definitely-when-not-booleanp
  (implies (not (booleanp x))
           (not (3definitely x)))
  :enable (3definitely
           3equiv))

(defrule 3definitely-when-not-booleanp-cheap
  (implies (not (booleanp x))
           (not (3definitely x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3definitely-when-not-booleanp)

(defruled 3fix-when-3definitely
  (implies (3definitely x)
           (equal (3fix x)
                  t))
  :enable 3definitely)

(defruled antimonotonicity-of-3definitely
  (implies (and (3info<= x0 x1)
                (3definitely x1))
           (3definitely x0))
  :enable (3definitely
           3info<=))

(defrule 3definitely-of-3join
  (equal (3definitely (3join x y))
         (and (3definitely x)
              (3definitely y)))
  :enable (3definitely
           3equiv
           3join))

(defrule 3definitely-of-3and
  (equal (3definitely (3and x y))
         (and (3definitely x)
              (3definitely y)))
  :enable (3definitely
           3equiv
           3and
           3fix
           3p))

(defrule 3definitely-of-3or
  (equal (3definitely (3or x y))
         (or (3definitely x)
             (3definitely y)))
  :enable (3definitely
           3equiv
           3or))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled 3possibly-when-3definitely
  (implies (3definitely x)
           (3possibly x))
  :enable (3possibly
           3definitely))

(defrule 3possibly-when-3definitely-forward-chaining
  (implies (3definitely x)
           (3possibly x))
  :rule-classes :forward-chaining
  :by 3possibly-when-3definitely)

(defruled 3fix-when-3possibly-and-not-3definitely
  (implies (and (3possibly x)
                (not (3definitely x)))
           (equal (3fix x)
                  :unknown))
  :enable (3possibly
           3definitely
           3fix
           3p))

(defrule 3possibly-of-3not
  (equal (3possibly (3not x))
         (not (3definitely x)))
  :enable (3possibly
           3definitely
           3equiv
           3not
           3fix
           3p))

(defrule 3definitely-of-3not
  (equal (3definitely (3not x))
         (not (3possibly x)))
  :enable (3possibly
           3definitely
           3not))

(defrule 3possibly-of-3xor
  (equal (3possibly (3xor x y))
         (or (and (3possibly x) (not (3definitely y)))
             (and (3possibly y) (not (3definitely x)))))
  :enable (3possibly
           3definitely
           3equiv
           3xor
           3fix
           3p))

(defrule 3definitely-of-3xor
  (equal (3definitely (3xor x y))
         (or (and (3definitely x) (not (3possibly y)))
             (and (3definitely y) (not (3possibly x)))))
  :enable (3possibly
           3definitely
           3equiv
           3xor
           3fix
           3p))

(defrule 3possibly-of-3implies
  (equal (3possibly (3implies x y))
         (implies (3definitely x)
                  (3possibly y))))

(defrule 3definitely-of-3implies
  (equal (3definitely (3implies x y))
         (implies (3possibly x)
                  (3definitely y))))

(defrule 3possibly-of-3iff
  (equal (3possibly (3iff x y))
         (or (and (3possibly x) (3possibly y))
             (and (not (3definitely x)) (not (3definitely y)))))
  :enable (3possibly
           3definitely
           3equiv
           3iff
           3fix
           3p))

(defrule 3definitely-of-3iff
  (equal (3definitely (3iff x y))
         (or (and (3definitely x) (3definitely y))
             (and (not (3possibly x)) (not (3possibly y)))))
  :enable (3possibly
           3definitely
           3equiv
           3iff
           3fix
           3p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3truth<
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare truth of @(see 3p)s."
  :long
  (xdoc::topstring-p
   "This is the strict truth order:
    @('nil') is below @(':unknown'), which is below @('t').
    It is the counterpart of the information order @(tsee 3info<).
    See @(see 3vl) for more detail.")
  (let ((x (3fix x))
        (y (3fix y)))
    (cond ((not x) (and y t))
          ((eq x :unknown) (eq y t))
          (t nil)))
  :inline t
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3truth<-type-prescription
  (booleanp (3truth< x y))
  :rule-classes ((:type-prescription :typed-term (3truth< x y))))

(defrule 3truth<-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3truth< x0 y)
                  (3truth< x1 y)))
  :rule-classes :congruence
  :enable 3truth<)

(defrule 3truth<-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3truth< x y0)
                  (3truth< x y1)))
  :rule-classes :congruence
  :enable 3truth<)

(defrule 3truth<-of-nil
  (equal (3truth< nil y)
         (and (3fix y) t))
  :enable 3truth<)

(defrule 3truth<-of-t
  (not (3truth< t y))
  :enable 3truth<)

(defrule 3truth<-of-arg1-and-nil
  (not (3truth< x nil))
  :enable 3truth<)

(defrule 3truth<-of-arg1-and-t
  (equal (3truth< x t)
         (not (equal (3fix x) t)))
  :enable (3truth<
           3fix
           3p))

(defrule irreflexivity-of-3truth<
  (not (3truth< x x))
  :enable 3truth<)

(defruled asymmetry-of-3truth<
  (implies (3truth< x y)
           (not (3truth< y x)))
  :enable 3truth<)

(defrule asymmetry-of-3truth<-forward-chaining
  (implies (3truth< x y)
           (not (3truth< y x)))
  :rule-classes :forward-chaining
  :by asymmetry-of-3truth<)

(defrule transitivity-of-3truth<
  (implies (and (3truth< x y)
                (3truth< y z))
           (3truth< x z))
  :enable 3truth<)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3truth<=
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare weak truth of @(see 3p)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "Recognizes values that are either @(tsee 3truth<) or @(tsee 3equiv).")
   (xdoc::p
    "This is the order under which
     @(tsee 3and) is the meet and @(tsee 3or) is the join,
     and under which both are monotone.
     It is characterized by the two boolean projections:
     @('x') is below @('y') exactly when
     @(tsee 3possibly) and @(tsee 3definitely) of @('x')
     each imply the same of @('y')."))
  (mbe :logic (or (equal (3fix x)
                         (3fix y))
                  (3truth< x y))
       :exec (or (eq x y)
                 (not x)
                 (eq y t)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable 3truth< 3fix 3p)))
  :type-prescription :none)

;;;;;;;;;;;;;;;;;;;;

(defrule 3truth<=-type-prescription
  (booleanp (3truth<= x y))
  :rule-classes ((:type-prescription :typed-term (3truth<= x y))))

(defrule 3truth<=-when-3equiv-of-arg1-congruence
  (implies (3equiv x0 x1)
           (equal (3truth<= x0 y)
                  (3truth<= x1 y)))
  :rule-classes :congruence
  :enable 3truth<=)

(defrule 3truth<=-when-3equiv-of-arg2-congruence
  (implies (3equiv y0 y1)
           (equal (3truth<= x y0)
                  (3truth<= x y1)))
  :rule-classes :congruence
  :enable 3truth<=)

(defrule 3truth<=-of-nil
  (3truth<= nil y)
  :enable 3truth<=)

(defrule 3truth<=-of-t
  (equal (3truth<= t y)
         (equal (3fix y) t))
  :enable (3truth<=
           3truth<
           3fix
           3p))

(defrule 3truth<=-of-arg1-and-nil
  (equal (3truth<= x nil)
         (not (3fix x)))
  :enable (3truth<=
           3truth<
           3fix
           3p))

(defrule 3truth<=-of-arg1-and-t
  (3truth<= x t)
  :enable (3truth<=
           3truth<
           3fix
           3p))

(defruled 3truth<=-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3truth<= x y)
                  (implies (double-rewrite x)
                           (double-rewrite y))))
  :enable (3truth<=
           3truth<
           3fix))

(defrule reflexivity-of-3truth<=
  (3truth<= x x)
  :enable 3truth<=)

(defruled antisymmetry-of-3truth<=-weak
  (implies (and (3truth<= x y)
                (3truth<= y x))
           (3equiv x y))
  :enable (3truth<=
           3truth<
           3equiv))

(defruled antisymmetry-of-3truth<=
  (equal (and (3truth<= x y)
              (3truth<= y x))
         (3equiv x y))
  :use antisymmetry-of-3truth<=-weak)

(defrule antisymmetry-of-3truth<=-forward-chaining
  (implies (and (3truth<= x y)
                (3truth<= y x))
           (3equiv x y))
  :rule-classes :forward-chaining
  :by antisymmetry-of-3truth<=-weak)

(defrule transitivity-of-3truth<=
  (implies (and (3truth<= x y)
                (3truth<= y z))
           (3truth<= x z))
  :enable (3truth<=
           3truth<
           3fix))

(defrule 3truth<=-when-3truth<
  (implies (3truth< x y)
           (3truth<= x y))
  :enable 3truth<=)

(defruled 3truth<-when-not-3truth<=
  (implies (not (3truth<= x y))
           (not (3truth< x y))))

(defrule 3truth<-when-not-3truth<=-forward-chaining
  (implies (not (3truth<= x y))
           (not (3truth< x y)))
  :rule-classes :forward-chaining
  :by 3truth<-when-not-3truth<=)

;; The lattice structure.

(defruled 3truth<=-becomes-3equiv-of-3and
  (equal (3truth<= x y)
         (3equiv (3and x y) x))
  :enable (3truth<=
           3truth<
           3and
           3equiv
           3fix
           3p))

(defruled 3truth<=-becomes-3equiv-of-3or
  (equal (3truth<= x y)
         (3equiv (3or x y) y))
  :enable (3truth<=
           3truth<
           3or
           3equiv
           3fix
           3p))

(defrule 3truth<=-of-3and
  (and (3truth<= (3and x y) x)
       (3truth<= (3and x y) y))
  :enable (3truth<=
           3truth<
           3and
           3fix
           3p))

(defrule 3truth<=-of-arg1-and-3or
  (and (3truth<= x (3or x y))
       (3truth<= y (3or x y)))
  :enable (3truth<=
           3truth<
           3or
           3fix
           3p))

(defrule truth-monotonicity-of-3and
  (implies (and (3truth<= x0 x1)
                (3truth<= y0 y1))
           (3truth<= (3and x0 y0) (3and x1 y1)))
  :enable (3truth<=
           3truth<
           3and
           3fix
           3p))

(defrule truth-monotonicity-of-3or
  (implies (and (3truth<= x0 x1)
                (3truth<= y0 y1))
           (3truth<= (3or x0 y0) (3or x1 y1)))
  :enable (3truth<=
           3truth<
           3or
           3fix
           3p))

(defrule 3truth<=-of-3not
  (equal (3truth<= (3not x) (3not y))
         (3truth<= y x))
  :enable (3truth<=
           3truth<
           3not
           3fix
           3p))

;; The boolean projections.

(defruled 3truth<=-becomes-3possibly-and-3definitely
  (equal (3truth<= x y)
         (and (implies (3possibly x) (3possibly y))
              (implies (3definitely x) (3definitely y))))
  :enable (3truth<=
           3truth<
           3possibly
           3definitely
           3equiv
           3fix
           3p))

(defrule 3possibly-when-3truth<=
  (implies (and (3truth<= x y)
                (3possibly x))
           (3possibly y))
  :use 3truth<=-becomes-3possibly-and-3definitely)

(defrule 3definitely-when-3truth<=
  (implies (and (3truth<= x y)
                (3definitely x))
           (3definitely y))
  :use 3truth<=-becomes-3possibly-and-3definitely)

;; The relation to implication: the truth order sits strictly between the two
;; projections of 3implies.

(defruled 3truth<=-when-3definitely-of-3implies
  (implies (3definitely (3implies x y))
           (3truth<= x y))
  :enable (3truth<=
           3truth<
           3implies
           3not
           3or
           3definitely
           3equiv
           3fix
           3p))

(defrule 3truth<=-when-3definitely-of-3implies-forward-chaining
  (implies (3definitely (3implies x y))
           (3truth<= x y))
  :rule-classes :forward-chaining
  :by 3truth<=-when-3definitely-of-3implies)

(defruled 3possibly-of-3implies-when-3truth<=
  (implies (3truth<= x y)
           (3possibly (3implies x y)))
  :enable (3truth<=
           3truth<
           3implies
           3not
           3or
           3possibly
           3equiv
           3fix
           3p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 3and$
  :parents (3and)
  :short "A lazy variant of @(tsee 3and)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Logically, @('3and$') is @(tsee 3and),
     but in execution an argument is evaluated
     only if no earlier argument is @('nil').
     Theorems should be stated in terms of @(tsee 3and).")
   (xdoc::p
    "The macro expands to an @(tsee mbe)
     whose proof obligation is discharged by @('3and-of-nil')
     during guard verification.")))

(defmacro binary-3and$ (x y)
  `(mbe :logic (3and ,x ,y)
        :exec (let ((__3vl_3and$_temp ,x))
                (if __3vl_3and$_temp
                    (3and __3vl_3and$_temp ,y)
                  (mbe :logic (3and __3vl_3and$_temp ,y)
                       :exec nil)))))

(defmacro 3and$ (&rest rest)
  (cond ((endp rest) t)
        ((endp (cdr rest)) `(3fix ,(car rest)))
        ((endp (cddr rest)) `(binary-3and$ ,(car rest) ,(cadr rest)))
        (t `(binary-3and$ ,(car rest) (3and$ ,@(cdr rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 3or$
  :parents (3or)
  :short "A lazy variant of @(tsee 3or)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Logically, @('3or$') is @(tsee 3or),
     but in execution an argument is evaluated
     only if no earlier argument is @('t').
     Theorems should be stated in terms of @(tsee 3or).")
   (xdoc::p
    "The macro expands to an @(tsee mbe)
     whose proof obligation is discharged by @('3or-of-t')
     during guard verification.")))

(defmacro binary-3or$ (x y)
  `(mbe :logic (3or ,x ,y)
        :exec (let ((__3vl_3or$_temp ,x))
                (if (eq __3vl_3or$_temp t)
                    (mbe :logic (3or __3vl_3or$_temp ,y)
                         :exec t)
                  (3or __3vl_3or$_temp ,y)))))

(defmacro 3or$ (&rest rest)
  (cond ((endp rest) nil)
        ((endp (cdr rest)) `(3fix ,(car rest)))
        ((endp (cddr rest)) `(binary-3or$ ,(car rest) ,(cadr rest)))
        (t `(binary-3or$ ,(car rest) (3or$ ,@(cdr rest))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 3implies$
  :parents (3implies)
  :short "A lazy variant of @(tsee 3implies)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Logically, @('3implies$') is @(tsee 3implies),
     but in execution the second argument is evaluated
     only if the first is not @('nil').
     Theorems should be stated in terms of @(tsee 3implies).")
   (xdoc::p
    "The macro expands to an @(tsee mbe)
     whose proof obligation is discharged by @('3implies-of-nil')
     during guard verification.")))

(defmacro 3implies$ (x y)
  `(mbe :logic (3implies ,x ,y)
        :exec (let ((__3vl_3implies$_temp ,x))
                (if __3vl_3implies$_temp
                    (3implies __3vl_3implies$_temp ,y)
                  (mbe :logic (3implies __3vl_3implies$_temp ,y)
                       :exec t)))))
