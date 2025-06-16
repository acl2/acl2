; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "if")
(include-book "if-with-coeffs")
(include-book "field-square")
(include-book "field-mul")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This family of gadgets handles raising a field constant to a positive integer
; expressed as a list of bits.  It is similar to field-pow-bits-gadget except
;
; * this is a family of gadgets, since the R1CS changes based on the constant;
;
; * the constraint pattern is abbreviated, since the constant base is folded in.

; Derivation.

; 1. Pattern from field-pow-bits-gadget
;
; In field-pow-bits-gadget, the "optimized" calculation is
;
;   r(n-1) = IF y(n-1) THEN x ELSE 1
;
;   s(n-2) = r(n-1) * r(n-1)
;   p(n-2) = x * s(n-2)
;   r(n-2) = IF y(n-2) THEN p(n-2) ELSE s(n-2)
;
;   ...
;
;   s(0) = r(1) * r(1)
;   p(0) = x * s(0)
;   r(0) = IF y(0) THEN p(0) ELSE s(0)

; 2. Simplification from field-pow-bits-gadget
;
; Since x is a constant, we do not need the ps, so the above constraints
; simplify to:
;
;   r(n-1) = IF y(n-1) THEN x ELSE 1
;
;   s(n-2) = r(n-1) * r(n-1)
;   r(n-2) = IF y(n-2) THEN x*s(n-2) ELSE s(n-2)
;
;   ...
;
;   s(0) = r(1) * r(1)
;   r(0) = IF y(0) THEN x*s(0) ELSE s(0)

; 3. Optimization of first three constraints.
;
; Let's look at the first constraint in more depth.
;
;   r(n-1) = IF y(n-1) THEN x ELSE 1
;
; is expressed as the ternary constraint:
;
;   y(n-1) * (x - 1) = (r(n-1) - 1)
;
; Since x is a constant, we replace (x - 1) by the constant X-1,
; so this first constraint becomes
;
;   X-1.y(n-1) = r(n-1) - 1
;
; Solving for r(n-1), we can substitute (X-1.y(n-1) + 1)
; into the next constraint, so the first 3 constraints
; become these two:
;
;   s(n-2) = (X-1.y(n-1) + 1) * (X-1.y(n-1) + 1)
;   r(n-2) = IF y(n-2) THEN x*s(n-2) ELSE s(n-2)
;
; 4. Summary
;
;   s(n-2) = (X-1.y(n-1) + 1) * (X-1.y(n-1) + 1)
;   r(n-2) = IF y(n-2) THEN x*s(n-2) ELSE s(n-2)
;
;   s(n-3) = r(n-2) * r(n-2)
;   r(n-3) = IF y(n-3) THEN x*s(n-3) ELSE s(n-3)
;
;   ...
;
;   s(0) = r(1) * r(1)
;   r(0) = IF y(0) THEN x*s(0) ELSE s(0)
;
; Constraint count:
;   2*(n-1) = 504 (assuming n is 253, the case we are most interested in)
; Variables:
;   We start out with n vars in ys;
;   there are n-1 ss and rs.
;
; 5. Other notes
;
; * SnarkVM uses the variable x0 to represent the constant 1
;   in the first constraint.  We have seen this previously.
;   Here we will call it "unitvar".

;;;;;;;;;;;;;;;;;;;;

; Support for the first constraint.
; The Overall 1st constraint comes from:
;   s(n-2) = (X-1.y(n-1) + 1) * (X-1.y(n-1) + 1)
; In this case, we replace `1` by unitvar
; since that is what we are seeing from SnarkVM.
; (We must constrain unitvar to be the constant 1
; when evaluating these circuits on concrete values.)
;
; This custom gadget equates the outout variable r
; to the square of (kx + 1), where `1` is actually a variable
; (the `unitvar`) that must be constrained to one somewhere else.
(define field-square-of-kx+unit-gadget ((k natp)
                                        (x symbolp)
                                        (unitvar symbolp)
                                        (r symbolp))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list
   (r1cs::make-r1cs-constraint
    :a (list (list k x)
             (list 1 unitvar))
    :b (list (list k x)
             (list 1 unitvar))
    :c (list (list 1 r)))))

(defruled field-square-of-kx+unit-gadget-to-square
  (implies (and (pfield::fep k p)
                (symbolp x)
                (symbolp unitvar)
                (symbolp r)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg unitvar)
                (r1cs::valuation-bindsp asg r))
           (b* ((x$ (lookup-equal x asg))
                (unitvar$ (lookup-equal unitvar asg))
                (r$ (lookup-equal r asg)))
             (implies (equal unitvar$ 1)
                      (equal (r1cs::r1cs-constraints-holdp
                              (field-square-of-kx+unit-gadget
                               k x unitvar r)
                              asg p)
                             (equal r$ (pfield::mul
                                        (pfield::add
                                         (pfield::mul k x$ p)
                                         unitvar$ p)
                                        (pfield::add
                                         (pfield::mul k x$ p)
                                         unitvar$ p)
                                        p))))))
  :do-not-induct t
  :enable (field-square-of-kx+unit-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product)
  :prep-books
  ((local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))))

;;;;;;;;;;;;;;;;;;;;

; the main gadget definition

(define field-const-pow-bits-gadget ((x (pfield::fep x p))
                                     (unitvar symbolp)
                                     (ys symbol-listp)
                                     (ss symbol-listp)
                                     (rs symbol-listp)
                                     (p primep))
  ;; We ignore the base case for very small length of ys
  ;; and simply require that there be at least 3 ys.
  :guard (and (consp ys) (consp (cdr ys)) (consp (cddr ys))
              (equal (len ss) (1- (len ys)))
              (equal (len rs) (1- (len ys))))
  :returns (constraints r1cs::r1cs-constraint-listp :hyp :guard)
  (rev (field-const-pow-bits-gadget-aux x unitvar ys ss rs p))
  :prepwork
  ((define field-const-pow-bits-gadget-aux ((x (pfield::fep x p))
                                            (unitvar symbolp)
                                            (ys symbol-listp)
                                            (ss symbol-listp)
                                            (rs symbol-listp)
                                            (p primep))
     :guard (and (consp ys) (consp (cdr ys))
                 (equal (len ss) (1- (len ys)))
                 (equal (len rs) (1- (len ys))))
     :returns (constraints r1cs::r1cs-constraint-listp :hyp :guard)
     :measure (len ys)
     (cond ((not (mbt (consp (cdr ys)))) nil)

           ((endp (cddr ys))
            ;; If there are only two items left in ys, they are y(n-2) and y(n-1)
            ;; in that order; at the same time there will only be one item left
            ;; in each of rs and ss, rs(n-2) and ss(n-2), respectively.

            (append
             ;; The end case is the first two constraints, in reverse order.
             ;; Overall 2nd constraint comes from:
             ;;   r(n-2) = IF y(n-2) THEN x*s(n-2) ELSE s(n-2)
             (if-with-coeffs-samevar-gadget (car ys)
                                            x
                                            (car ss)
                                            1
                                            (car rs)
                                            p)

             ;; The overall 1st constraint:
             ;;   s(n-2) = (X-1.y(n-1) + 1) * (X-1.y(n-1) + 1)
             ;; (where the `1`s are unitvar).
             ;; If X-1 is 0, this reduces to
             ;;   s(n-2) = unitvar*unitvar
             (if (equal x 1)
                 (field-square-gadget unitvar (car ss))
               ;; otherwise we use the custom gadget defined above
               (field-square-of-kx+unit-gadget
                (pfield::sub x 1 p) (cadr ys) unitvar (car ss)))
             ))

           (t (append

               (if-with-coeffs-samevar-gadget (car ys)
                                              x
                                              (car ss)
                                              1
                                              (car rs)
                                              p)

               (field-square-gadget (cadr rs) (car ss))

               (field-const-pow-bits-gadget-aux x
                                                unitvar
                                                (cdr ys)
                                                (cdr ss)
                                                (cdr rs)
                                                p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce a function that describes
; the recursive computation of the ss and rs values from x and ys.
; In the function name, 'sr' refers to Square and Result.

(local
 (define sr ((x (pfield::fep x p)) (ys bit-listp) (p primep))
   :guard (and (consp ys) (consp (cdr ys)))
   :returns (mv (ss (pfield::fe-listp ss p) :hyp (and (primep p)
                                                      (pfield::fep x p)))
                (rs (pfield::fe-listp rs p) :hyp (and (primep p)
                                                      (pfield::fep x p))))
   :measure (len ys)
   (let ((X-1 (pfield::sub x 1 p)))
     (cond ((not (mbt (consp (cdr ys)))) (mv nil nil))
           ((endp (cddr ys))
            (let* ((in-square (pfield::add (pfield::mul X-1 (cadr ys) p) 1 p))
                   (s[n-2] (pfield::mul in-square in-square p)))
              (if (equal (car ys) 1)
                  (mv (list s[n-2]) (list (pfield::mul x s[n-2] p)))
                (mv (list s[n-2]) (list s[n-2])))))
           (t (b* (((mv cdr-ss cdr-rs) (sr x (cdr ys) p))
                   (cadr-rs (car cdr-rs))
                   (car-ss (pfield::mul cadr-rs cadr-rs p))
                   (car-rs (if (equal (car ys) 1)
                               (pfield::mul x car-ss p)
                             car-ss)))
                (mv (cons car-ss cdr-ss)
                    (cons car-rs cdr-rs))))))

   ///

   (defret len-of-sr-ss
     (equal (len ss)
            (1- (len ys)))
     :hyp (consp ys))

   (defret len-of-sr-rs
     (equal (len rs)
            (1- (len ys)))
     :hyp (consp ys))

   (defret consp-of-sr-ss
     (equal (consp ss)
            (consp (cdr ys))))

   (defret consp-of-sr-rs
     (equal (consp rs)
            (consp (cdr ys))))))

; The following theorem links the gadget definition
; to the calculation described by the function sr.
; The proof is currently clumsy and verbose;
; it should be possible to make it simpler and shorter.

(defruledl field-const-pow-bits-gadget-aux-to-sr
  (implies (and (pfield::fep x p)
                (symbolp unitvar)
                (symbol-listp ys)
                (symbol-listp ss)
                (symbol-listp rs)
                (consp ys)
                (equal (len ss) (1- (len ys)))
                (equal (len rs) (1- (len ys)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg unitvar)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ss)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((unitvar$ (lookup-equal unitvar asg))
                (ys$ (lookup-equal-list ys asg))
                (ss$ (lookup-equal-list ss asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (and (equal unitvar$ 1)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (field-const-pow-bits-gadget-aux x unitvar ys ss rs p)
                                asg p)
                               (b* (((mv ss1$ rs1$) (sr x ys$ p)))
                                 (and (equal ss$ ss1$)
                                      (equal rs$ rs1$)))))))
  :induct (induction-schema ys ss rs)
  :hints ('(:use (base-case induction-step)))

  :prep-lemmas

  ((defun induction-schema (ys ss rs)
     (cond ((or (endp ys) (endp (cdr ys)) (endp (cddr ys))
                (endp ss)
                (endp rs))
            nil)
           (t (induction-schema (cdr ys) (cdr ss) (cdr rs)))))

   (defruled base-case
     (implies
      ;; condition for the base case:
      (or (endp ys) (endp (cdr ys)) (endp (cddr ys))
          (endp ss)
          (endp rs))
      ;; claim to prove:
      (implies (and (pfield::fep x p)
                    (symbolp unitvar)
                    (symbol-listp ys)
                    (symbol-listp ss)
                    (symbol-listp rs)
                    (consp ys)
                    (equal (len ss) (1- (len ys)))
                    (equal (len rs) (1- (len ys)))
                    (primep p)
                    (r1cs::r1cs-valuationp asg p)
                    (r1cs::valuation-bindsp asg unitvar)
                    (r1cs::valuation-binds-allp asg ys)
                    (r1cs::valuation-binds-allp asg ss)
                    (r1cs::valuation-binds-allp asg rs))
               (b* ((unitvar$ (lookup-equal unitvar asg))
                    (ys$ (lookup-equal-list ys asg))
                    (ss$ (lookup-equal-list ss asg))
                    (rs$ (lookup-equal-list rs asg)))
                 (implies (and (equal unitvar$ 1)
                               (bit-listp ys$))
                          (implies (r1cs::r1cs-constraints-holdp
                                    (field-const-pow-bits-gadget-aux
                                     x unitvar ys ss rs p)
                                    asg p)
                                   (b* (((mv ss1$ rs1$) (sr x ys$ p)))
                                     (and (equal ss$ ss1$)
                                          (equal rs$ rs1$))))))))
     :do-not-induct t
     :expand (sr x (lookup-equal-list ys asg) p)
     :enable (field-const-pow-bits-gadget-aux
              if-with-coeffs-samevar-gadget-to-if
              field-square-gadget-correctness
              field-square-of-kx+unit-gadget-to-square
              sr
              lookup-equal-list
              pfield::fep)
     :prep-books
     ((local (include-book "kestrel/arithmetic-light/mod" :dir :system)))
     :prep-lemmas
     ((defrule lemma1
        (implies (primep p)
                 (equal (equal (mod 2 p) 0)
                        (equal p 2))))
      (defrule lemma2
        (implies (primep p)
                 (equal (pfield::mul (pfield::add 1 (pfield::add 1 (+ -1 p) p)
                                                  p)
                                     (pfield::add 1 (pfield::add 1 (+ -1 p) p)
                                                  p)
                                     p)
                        1))
        :enable (pfield::add pfield::mul))))

   (defruled induction-step
     (implies
      ;; condition of the induction step (i.e. negation base case condition):
      (not (or (endp ys) (endp (cdr ys)) (endp (cddr ys))
               (endp ss)
               (endp rs)))
      (implies
       ;; induction hyp:
       (implies (and (pfield::fep x p)
                     (symbolp unitvar)
                     (symbol-listp (cdr ys))
                     (symbol-listp (cdr ss))
                     (symbol-listp (cdr rs))
                     (consp (cdr ys))
                     (equal (len (cdr ss)) (1- (len (cdr ys))))
                     (equal (len (cdr rs)) (1- (len (cdr ys))))
                     (primep p)
                     (r1cs::r1cs-valuationp asg p)
                     (r1cs::valuation-bindsp asg unitvar)
                     (r1cs::valuation-binds-allp asg (cdr ys))
                     (r1cs::valuation-binds-allp asg (cdr ss))
                     (r1cs::valuation-binds-allp asg (cdr rs)))
                (b* ((unitvar$ (lookup-equal unitvar asg))
                     (cdr-ys$ (lookup-equal-list (cdr ys) asg))
                     (cdr-ss$ (lookup-equal-list (cdr ss) asg))
                     (cdr-rs$ (lookup-equal-list (cdr rs) asg)))
                  (implies (and (equal unitvar$ 1)
                                (bit-listp cdr-ys$))
                           (implies (r1cs::r1cs-constraints-holdp
                                     (field-const-pow-bits-gadget-aux
                                      x unitvar (cdr ys) (cdr ss) (cdr rs) p)
                                     asg p)
                                    (b* (((mv cdr-ss1$ cdr-rs1$) (sr x cdr-ys$ p)))
                                      (and (equal cdr-ss$ cdr-ss1$)
                                           (equal cdr-rs$ cdr-rs1$)))))))
       ;; claim:
       (implies (and (pfield::fep x p)
                     (symbolp unitvar)
                     (symbol-listp ys)
                     (symbol-listp ss)
                     (symbol-listp rs)
                     (consp ys)
                     (equal (len ss) (1- (len ys)))
                     (equal (len rs) (1- (len ys)))
                     (primep p)
                     (r1cs::r1cs-valuationp asg p)
                     (r1cs::valuation-bindsp asg unitvar)
                     (r1cs::valuation-binds-allp asg ys)
                     (r1cs::valuation-binds-allp asg ss)
                     (r1cs::valuation-binds-allp asg rs))
                (b* ((unitvar$ (lookup-equal unitvar asg))
                     (ys$ (lookup-equal-list ys asg))
                     (ss$ (lookup-equal-list ss asg))
                     (rs$ (lookup-equal-list rs asg)))
                  (implies (and (equal unitvar$ 1)
                                (bit-listp ys$))
                           (implies (r1cs::r1cs-constraints-holdp
                                     (field-const-pow-bits-gadget-aux
                                      x unitvar ys ss rs p)
                                     asg p)
                                    (b* (((mv ss1$ rs1$) (sr x ys$ p)))
                                      (and (equal ss$ ss1$)
                                           (equal rs$ rs1$)))))))))
     :do-not-induct t
     :expand ((SR X (LOOKUP-EQUAL-LIST YS ASG) P)
              (FIELD-CONST-POW-BITS-GADGET-AUX X UNITVAR YS SS RS P)
              (LOOKUP-EQUAL-LIST SS ASG)
              (LOOKUP-EQUAL-LIST RS ASG))
     :enable (if-with-coeffs-samevar-gadget-to-if
              field-square-gadget-correctness
              car-of-lookup-equal-list
              lemma1
              lemma2
              lemma3
              lemma4
              lemma5
              lemma6
              lemma7)

     :prep-lemmas

     ((defrule lemma1
        (implies (bit-listp (lookup-equal-list vars asg))
                 (bit-listp (lookup-equal-list (cdr vars) asg)))
        :enable lookup-equal-list-of-cdr)

      (defrule lemma2
        (equal (consp (cdr (lookup-equal-list keys alist)))
               (consp (cdr keys)))
        :enable lookup-equal-list)

      (defrule lemma3
        (implies (and (bit-listp (lookup-equal-list ys asg))
                      (consp ys))
                 (bitp (lookup-equal (car ys) asg)))
        :enable lookup-equal-list)

      (defrule lemma4
        (implies (and (r1cs::valuation-binds-allp asg rs)
                      (consp (cddr ys))
                      (equal (len (cddr ys)) (len (cdr rs))))
                 (r1cs::valuation-bindsp asg (cadr rs))))

      (defrule lemma5
        (equal (SR X (LOOKUP-EQUAL-LIST (CDR YS) ASG) P)
               (SR X (cdr (LOOKUP-EQUAL-LIST YS ASG)) P))
        :enable lookup-equal-list-of-cdr)

      (defrule lemma6
        (implies (and (consp (cddr ys))
                      (equal (len (cddr ys)) (len (cdr rs))))
                 (equal (CAR (LOOKUP-EQUAL-LIST (CDR RS) ASG))
                        (LOOKUP-EQUAL (CADR RS) ASG)))
        :enable (car-of-lookup-equal-list))

      (defrule lemma7
        (implies (consp (cddr ys))
                 (consp (cddr (lookup-equal-list ys asg))))
        :enable lookup-equal-list)))))

; The following theorem shows that the function sr defined above
; correctly calculates the desired result,
; i.e. x raised to the exponent described by the bits ys.

(defruledl sr-correctness
  (implies (and (pfield::fep x p)
                (bit-listp ys)
                (primep p)
                (oddp p)
                (consp ys)
                (consp (cdr ys)))
           (b* (((mv & rs) (sr x ys p)))
             (equal (car rs)
                    (pfield::pow x (lebits=>nat ys) p))))
  :induct (sr x ys p)
  :enable sr
  :hints ('(:use (induction-step base-case)))

  :prep-lemmas

  ((defruled induction-step-with-cons
     (implies
      ;; condition for the induction step (i.e. negation of base case condition):
      (and (consp ys)
           (consp (cdr ys)))
      (implies
       ;; induction hyp:
       (implies (and (pfield::fep x p)
                     (bit-listp ys)
                     (primep p)
                     (consp ys)
                     (consp (cdr ys)))
                (b* (((mv & rs) (sr x ys p)))
                  (equal (car rs)
                         (pfield::pow x (lebits=>nat ys) p))))
       ;; claim:
       (implies (and (pfield::fep x p)
                     (bit-listp (cons y ys))
                     (primep p)
                     (consp (cons y ys))
                     (consp ys))
                (b* (((mv & rs) (sr x (cons y ys) p)))
                  (equal (car rs)
                         (pfield::pow x (lebits=>nat (cons y ys)) p))))))
     :do-not-induct t
     :enable (acl2::lebits=>nat-of-cons)
     :expand (sr x (cons y ys) p)
     :disable bitp
     :prep-lemmas
     ((defrule lemma
        (implies (and (integerp p)
                      (< 1 p)
                      (natp a)
                      (pfield::fep x p))
                 (equal (pfield::pow x (* 2 a) p)
                        (pfield::mul (pfield::pow x a p)
                                     (pfield::pow x a p)
                                     p)))
        :use (:instance pfield::pow-of-+ (a x) (b a) (c a) (p p))
        :cases ((equal (* 2 a) (+ a a)))
        :disable pfield::pow-of-+)))

   (defruled induction-step
     (implies
      ;; condition for the induction step:
      (and (consp (cdr ys))
           (consp (cddr ys)))
      (implies
       ;; induction hyp:
       (implies (and (pfield::fep x p)
                     (bit-listp (cdr ys))
                     (primep p)
                     (consp (cdr ys))
                     (consp (cdr (cdr ys))))
                (b* (((mv & cdr-rs) (sr x (cdr ys) p)))
                  (equal (car cdr-rs)
                         (pfield::pow x (lebits=>nat (cdr ys)) p))))
       ;; claim:
       (implies (and (pfield::fep x p)
                     (bit-listp ys)
                     (primep p)
                     (consp ys)
                     (consp (cdr ys)))
                (b* (((mv & rs) (sr x ys p)))
                  (equal (car rs)
                         (pfield::pow x (lebits=>nat ys) p))))))
     :use (:instance induction-step-with-cons
                     (y (car ys)) (ys (cdr ys))))

   (defruled base-case
     (implies
      ;; condition for the base case (i.e. negation of induction step condition):
      (not (and (consp (cdr ys))
                (consp (cddr ys))))
      ;; claim:
      (implies (and (pfield::fep x p)
                    (bit-listp ys)
                    (primep p)
                    (oddp p)
                    (consp ys)
                    (consp (cdr ys)))
               (b* (((mv & rs) (sr x ys p)))
                 (equal (car rs)
                        (pfield::pow x (lebits=>nat ys) p)))))
     :do-not-induct t
     :enable (sr
              lebits=>nat
              acl2::lendian=>nat
              acl2::dab-digit-fix
              acl2::dab-digitp
              lemma-pow2
              lemma-pow3
              lemma-p2-m2-alt)
     :cases ((equal ys '(0 0))
             (equal ys '(0 1))
             (equal ys '(1 0))
             (equal ys '(1 1)))
     :prep-books
     ((include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

     :prep-lemmas

     ((defruled lemma-pow3
        (implies (primep p)
                 (equal (PFIELD::POW X 3 P)
                        (PFIELD::MUL X (PFIELD::MUL X X P) P)))
        :enable pfield::pow
        :expand ((PFIELD::POW X 3 P)
                 (PFIELD::POW X 2 P)))

      (defruled lemma-pow2
        (implies (primep p)
                 (equal (PFIELD::POW X 2 P)
                        (PFIELD::MUL X X P)))
        :enable pfield::pow
        :expand ((PFIELD::POW X 2 P)))

      (defruled lemma-p2-m2-alt
        (implies (and (primep p)
                      (oddp p)
                      (pfield::fep x p))
                 (equal (pfield::add 2 (pfield::add -2 x p) p)
                        x))
        :enable (pfield::add))))))

; We put together the previous two theorems
; to prove the soundness of the gadget.

(defruled field-const-pow-bits-soundness
  (implies
   (and (pfield::fep x p)
        (symbolp unitvar)
        (symbol-listp ys)
        (symbol-listp ss)
        (symbol-listp rs)
        (consp ys)
        (consp (cdr ys))
        (equal (len ss) (1- (len ys)))
        (equal (len rs) (1- (len ys)))
        (primep p)
        (oddp p)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg unitvar)
        (r1cs::valuation-binds-allp asg ys)
        (r1cs::valuation-binds-allp asg ss)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((unitvar$ (lookup-equal unitvar asg))
        (ys$ (lookup-equal-list ys asg))
        (rs$ (lookup-equal-list rs asg)))
     (implies (and (equal unitvar$ 1)
                   (bit-listp ys$))
              (implies (r1cs::r1cs-constraints-holdp
                        (field-const-pow-bits-gadget x unitvar ys ss rs p)
                        asg p)
                       (equal (car rs$)
                              (pfield::pow x (lebits=>nat ys$) p))))))
  :do-not-induct t
  :enable field-const-pow-bits-gadget
  :use (field-const-pow-bits-gadget-aux-to-sr
        (:instance sr-correctness
                   (ys (lookup-equal-list ys asg))))

  :prep-lemmas
  ((defrule lemma-cdr
     (equal (consp (cdr (lookup-equal-list keys alist)))
            (consp (cdr keys)))
     :enable lookup-equal-list)))
