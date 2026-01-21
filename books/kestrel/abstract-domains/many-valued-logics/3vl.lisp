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

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc 3vl
  :parents (many-valued-logics)
  :short "A three-valued logic."
  :long
  (xdoc::topstring
    (xdoc::p
      "This logic extends booleans and boolean operations with a third value,
       @(':unknown'). As the symbol name suggests, this value indicates the
       result may be @('nil') or @('t'), but we are uncertain which. You might
       also read it as ``maybe''.")
    (xdoc::p
      "When applied to boolean values, the three-valued logic operators behave
       exactly like their traditional boolean counterparts.")
    (xdoc::p
      "The partial order @(tsee 3<) relates more specific values to less
       specific values. More specifically, we have just @('(3< nil :unknown)')
       and @('(3< t :unknown)'). This three-valued logic forms a
       join-semilattice, where @(tsee 3join) is the join.")
    (xdoc::p
      "(There is no meet, because there is no lower bound for @('nil') and
       @('t'). If we wished to add a meet, we would need to introduce a bottom
       element, which we might call ``contradiction''. The interpretation of
       this element is more complicated &mdash; it would indicate that the
       value is <i>both</i> @('nil') <i>and</i> @('t'). This would make a
       sensible four-valued logic, which we may add at some point in the
       future. For now, we avoid the complication.)")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3p (x)
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Recognizer for three-value logic values."
  :long
  (xdoc::topstring
   (xdoc::p
     "Checks that the recognized value is @('nil'), @('t'), or @(':unknown')."))
  (or (eq x t)
      (eq x nil)
      (eq x :unknown)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3p)))

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
  (xdoc::topstring
   (xdoc::p
     "If the argument is not a @(see 3p), we default to @(':unknown')."))
  (mbe :logic (if (3p x)
                  x
                :unknown)
       :exec x)
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3fix)))

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
       x)
  :enable 3fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3=
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Equivalence of @(see 3p)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "This is a typical equality of fixers. Note that this is <i>not</i> the
      same as @(tsee 3iff)."))
  (eq (3fix x)
      (3fix y))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3=)))

(defrule 3=-type-prescription
  (booleanp (3= x y))
  :rule-classes ((:type-prescription :typed-term (3= x y))))

(defequiv 3=
  :hints (("Goal" :in-theory (enable 3=))))

(defrule 3fix-when-3=-congruence
  (implies (3= tri0 tri1)
           (equal (3fix tri0)
                  (3fix tri1)))
  :rule-classes :congruence
  :enable 3=)

(defrule 3fix-under-3=
  (3= (3fix x)
      x)
  :enable 3=)

(defrule iff-when-3=
  (implies (3= x y)
           (iff x y))
  :rule-classes :refinement
  :enable 3=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3<
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare specificity of @(see 3p)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "This forms a join-semilattice on @(see 3p)s. See @(see 3vl) for more
      detail."))
  (let ((x (3fix x))
        (y (3fix y)))
    (and (not (eq x :unknown))
         (eq y :unknown)))
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3<)))

(defrule 3<-type-prescription
  (booleanp (3< x y))
  :rule-classes ((:type-prescription :typed-term (3< x y))))

(defrule 3<-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3< x0 y)
                  (3< x1 y)))
  :rule-classes :congruence
  :enable 3<)

(defrule 3<-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
           (equal (3< x y0)
                  (3< x y1)))
  :rule-classes :congruence
  :enable 3<)

(defruled 3<-when-booleanp-of-arg1
  (implies (booleanp x)
           (equal (3< x y)
                  (not (booleanp y))))
  :enable 3<)

(defrule 3<-when-booleanp-of-arg1-cheap
  (implies (booleanp x)
           (equal (3< x y)
                  (not (booleanp y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<-when-booleanp-of-arg1)

(defruled 3<-when-booleanp-of-arg2
  (implies (booleanp y)
           (not (3< x y)))
  :enable 3<)

(defrule 3<-when-booleanp-of-arg2-cheap
  (implies (booleanp y)
           (not (3< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<-when-booleanp-of-arg2)

(defruled 3<-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (not (3< x y)))
  :enable 3<)

(defrule 3<-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (not (3< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<-when-not-booleanp-of-arg1)

(defruled 3<-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (equal (3< x y)
                  (booleanp x)))
  :enable 3<)

(defrule 3<-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (equal (3< x y)
                  (booleanp x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<-when-not-booleanp-of-arg2)

(defrule irreflexivity-of-3<
  (not (3< x x))
  :enable 3<)

(defruled asymmetry-of-3<
  (implies (3< x y)
           (not (3< y x)))
  :enable 3<)

(defrule asymmetry-of-3<-forward-chaining
  (implies (3< x y)
           (not (3< y x)))
  :rule-classes :forward-chaining
  :by asymmetry-of-3<)

(defruled 3fix-when-3<
  (implies (3< x y)
           (equal (3fix y)
                  :unknown))
  :enable 3<)

(defrule arg2-under-3=-when-3<-forward-chaining
  (implies (3< x y)
           (3= y :unknown))
  :rule-classes :forward-chaining
  :enable (3<
           3=))

;; 3< is technically transitive, but it isn't a useful rule, since it is
;; trivialized by arg2-under-3=-when-3<-forward-chaining.
(defruled transitivity-of-3<
  (implies (and (3< x y)
                (3< y z))
           (3< x z)))

(defruled booleanp-when-3<
  (implies (3< x y)
           (booleanp x))
  :enable 3<)

(defrule booleanp-when-3<-forward-chaining
  (implies (3< x y)
           (booleanp x))
  :rule-classes :forward-chaining
  :by booleanp-when-3<)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define 3<=
  ((x 3p)
   (y 3p))
  :returns (yes/no booleanp)
  :parents (3vl)
  :short "Compare weak specificity of @(see 3p)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Recognizes values that are either @(tsee 3<) or @(tsee 3=)."))
  (mbe :logic (or (equal (3fix x)
                         (3fix y))
                  (3< x y))
       :exec (or (eq x y)
                 (eq y :unknown)))
  :inline t
  :guard-hints (("Goal" :in-theory (enable 3<))))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3<=)))

(defrule 3<=-type-prescription
  (booleanp (3<= x y))
  :rule-classes ((:type-prescription :typed-term (3<= x y))))

(defrule 3<=-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3<= x0 y)
                  (3<= x1 y)))
  :rule-classes :congruence
  :enable 3<=)

(defrule 3<=-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
           (equal (3<= x y0)
                  (3<= x y1)))
  :rule-classes :congruence
  :enable 3<=)

(defruled 3<=-when-booleanp-of-arg2
  (implies (booleanp y)
           (equal (3<= x y)
                  (equal x y)))
  :enable 3<=)

(defrule 3<=-when-booleanp-of-arg2-cheap
  (implies (booleanp y)
           (equal (3<= x y)
                  (equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<=-when-booleanp-of-arg2)

(defruled 3<=-when-not-booleanp-of-arg1
  (implies (not (booleanp x))
           (equal (3<= x y)
                  (not (booleanp y))))
  :enable 3<=)

(defrule 3<=-when-not-booleanp-of-arg1-cheap
  (implies (not (booleanp x))
           (equal (3<= x y)
                  (not (booleanp y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<=-when-not-booleanp-of-arg1)

(defruled 3<=-when-not-booleanp-of-arg2
  (implies (not (booleanp y))
           (3<= x y))
  :enable 3<=)

(defrule 3<=-when-not-booleanp-of-arg2-cheap
  (implies (not (booleanp y))
           (3<= x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by 3<=-when-not-booleanp-of-arg2)

(defruled 3<=-of-nil
  (equal (3<= nil y)
         (not (equal y t)))
  :enable (3<=
           booleanp))

(defruled 3<=-of-t
  (equal (3<= t y)
         (and y t))
  :enable 3<=)

(defrule reflexivity-of-3<=
  (3<= x x)
  :enable 3<=)

(defruled antisymmetry-of-3<=-weak
  (implies (and (3<= x y)
                (3<= y x))
           (3= x y))
  :enable (3<=
           3=))

(defruled antisymmetry-of-3<=
  (equal (and (3<= x y)
              (3<= y x))
         (3= x y))
  :use antisymmetry-of-3<=-weak)

(defrule antisymmetry-of-3<=-forward-chaining
  (implies (and (3<= x y)
                (3<= y x))
           (3= x y))
  :rule-classes :forward-chaining
  :by antisymmetry-of-3<=-weak)

(defrule transitivity-of-3<=
  (implies (and (3<= x y)
                (3<= y z))
           (3<= x z))
  :enable (3<=
           3fix))

(defrule 3<=-when-3<
  (implies (3< x y)
           (3<= x y))
  :enable 3<=)

(defruled 3<-when-not-3<=
  (implies (not (3<= x y))
           (not (3< x y))))

(defrule 3<-when-not-3<=-forward-chaining
  (implies (not (3<= x y))
           (not (3< x y)))
  :rule-classes :forward-chaining
  :by 3<-when-not-3<=)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection 3join
  :parents (3vl)
  :short "The join on the @(tsee 3<) semilattice."

  (define binary-3join$inline
    ((x 3p)
     (y 3p))
    :returns (join 3p)
    (let ((x (3fix x))
          (y (3fix y)))
      (if (eq x y)
          x
        :unknown))
    ///

    (defmacro 3join (x &rest rest)
      (if (endp rest)
          (cons '3fix (list x))
        (xxxjoin 'binary-3join$inline (cons x rest))))

    (add-macro-fn 3join binary-3join$inline t)))

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3join)))

(defrule 3join-type-prescription
  (3p (3join x y))
  :rule-classes ((:type-prescription :typed-term (3join x y))))

(defrule 3join-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3join x0 y)
                  (3join x1 y)))
  :rule-classes :congruence
  :enable 3join)

(defrule 3join-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
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

(defruled monotinicity-of-3join-left
  (implies (and (3<= x0 x1))
           (3<= (3join x0 y)
                (3join x1 y)))
  :enable 3join)

(defruled monotinicity-of-3join-right
  (implies (and (3<= y0 y1))
           (3<= (3join x y0)
                (3join x y1)))
  :enable 3join)

(defrule monotonicity-of-3join
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3join x0 y0)
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
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3not)))

(defrule 3not-type-prescription
  (3p (3not x))
  :rule-classes ((:type-prescription :typed-term (3not x))))

(defrule 3not-when-3=-congruence
  (implies (3= x0 x1)
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
  (implies (3<= x0 x1)
           (3<= (3not x0)
                (3not x1)))
  :enable (3not
           3<=
           3<))

(defrule monotonicity-of-3not
  (equal (3<= (3not x0)
              (3not x1))
         (3<= x0 x1))
  :enable (3not
           3fix
           3p))

(defruled 3not-when-booleanp
  (implies (booleanp x)
           (equal (3not x)
                  (not x)))
  :enable 3not)

(defrule 3not-when-booleanp-cheap
  (implies (booleanp x)
           (equal (3not x)
                  (not x)))
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

(in-theory (disable (:t 3and)))

(defrule 3and-type-prescription
  (3p (3and x y))
  :rule-classes ((:type-prescription :typed-term (3and x y))))

(defrule 3and-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3and x0 y)
                  (3and x1 y)))
  :rule-classes :congruence
  :enable 3and)

(defrule 3and-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
           (equal (3and x y0)
                  (3and x y1)))
  :rule-classes :congruence
  :enable 3and)

(defrule booleanp-of-3and
  (equal (booleanp (3and x y))
         (or (not x)
             (not y)
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
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3and x0 y0)
                (3and x1 y1)))
  :enable (3and
           3<=
           3<))

(defruled 3and-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3and x y)
                  (and x y)))
  :enable 3and)

(defrule 3and-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3and x y)
                  (and x y)))
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

(in-theory (disable (:t 3or)))

(defrule 3or-type-prescription
  (3p (3or x y))
  :rule-classes ((:type-prescription :typed-term (3or x y))))

(defrule 3or-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3or x0 y)
                  (3or x1 y)))
  :rule-classes :congruence
  :enable 3or)

(defrule 3or-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
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
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3or x0 y0)
                (3or x1 y1)))
  :enable (3or
           3<=
           3<))

(defruled 3or-when-booleanp
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3or x y)
                  (or x y)))
  :enable 3or)

(defrule 3or-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3or x y)
                  (or x y)))
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

(in-theory (disable (:t 3xor)))

(defrule 3xor-type-prescription
  (3p (3xor x y))
  :rule-classes ((:type-prescription :typed-term (3xor x y))))

(defrule 3xor-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3xor x0 y)
                  (3xor x1 y)))
  :rule-classes :congruence
  :enable 3xor)

(defrule 3xor-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
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

(defrule 3xor-of-arg1-or-nil
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
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3xor x0 y0)
                (3xor x1 y1)))
  :enable (3xor
           3<=
           3<))

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
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(in-theory (disable (:t 3implies)))

(defrule 3implies-type-prescription
  (3p (3implies x y))
  :rule-classes ((:type-prescription :typed-term (3implies x y))))

(defrule 3implies-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3implies x0 y)
                  (3implies x1 y)))
  :rule-classes :congruence
  :enable 3implies)

(defrule 3implies-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
           (equal (3implies x y0)
                  (3implies x y1)))
  :rule-classes :congruence
  :enable 3implies)

(defrule booleanp-of-3implies
  (equal (booleanp (3implies x y))
         (or (not x)
             (equal y t)
             (and (equal x t)
                  (not y))))
  :enable (3implies
           3fix
           3p))

(defrule 3implies-of-nil
  (equal (3implies nil y)
         t)
  :enable 3implies)

(defrule 3implies-of-arg1-or-nil
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

(defrule 3implies-of-arg1-or-t
  (equal (3implies x t)
         t)
  :enable 3implies)

(defrule monotonicity-of-3implies
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3implies x0 y0)
                (3implies x1 y1)))
  :enable (3implies
           3<=
           3<))

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
                  (implies x y))))

(defrule 3implies-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3implies x y)
                  (implies x y)))
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

(in-theory (disable (:t 3iff)))

(defrule 3iff-type-prescription
  (3p (3iff x y))
  :rule-classes ((:type-prescription :typed-term (3iff x y))))

(defrule 3iff-when-3=-of-arg1-congruence
  (implies (3= x0 x1)
           (equal (3iff x0 y)
                  (3iff x1 y)))
  :rule-classes :congruence
  :enable 3iff)

(defrule 3iff-when-3=-of-arg2-congruence
  (implies (3= y0 y1)
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
  (implies (and (3<= x0 x1)
                (3<= y0 y1))
           (3<= (3iff x0 y0)
                (3iff x1 y1)))
  :enable (3iff
           3<=
           3<))

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
                  (iff x y))))

(defrule 3iff-when-booleanp-cheap
  (implies (and (booleanp x)
                (booleanp y))
           (equal (3iff x y)
                  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :by 3iff-when-booleanp)
