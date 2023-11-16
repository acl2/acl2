; Examples of Compositional Verification of R1CS Gadgets
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Aleo Systems Inc. (https://www.aleo.org)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)
;          Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ZKPAPER")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/list-fix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains some of the supporting materials for
; the ACL2-2023 Workshop paper "Formal Verification of Zero-Knowledge Circuits"
; by A. Coglio, E. McCarthy, and E. Smith.

; This file contains the formal details, overviewed in Section 5.5,
; of the example gadgets described in Section 2,
; formalized and verified compositionally in R1CS form.

; This file may be moved to the R1CS library at some point.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This lifts lookup-equal to lists.
; It probably belongs to the alists-light library.

(define lookup-equal-list (keys alist)
  :guard (and (true-listp keys) (alistp alist))
  :returns vals
  (cond ((endp keys) nil)
        (t (cons (lookup-equal (car keys) alist)
                 (lookup-equal-list (cdr keys) alist)))))

(defrule len-of-lookup-equal-list
  (equal (len (lookup-equal-list keys alist))
         (len keys))
  :induct t
  :enable lookup-equal-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Both the gadget in Figure 3 and the gadget in Figure 4
; include boolean constraints of the form (<var>) (1 - <var>) = (0).
; Even though this is a simple constraint,
; it makes sense to introduce a gadget (family) for this.
; It is also a very simple gadget, which  makes for a good first example.

; The gadget family is parameterized over the choice of the (only) variable.
; This way, if different instances of this gadget
; are used within a larger gadget,
; different variable names can be used for the different instances.

; The (only) constraint of this gadget is built directly by this function,
; via the make-r1cs-constraint constructor of R1CS constraints.

; The guard of the function just requires the variable name to be a symbol.
; The return theorem shows that the function produces a list of constraints.

(define boolean-assert-gadget ((x symbolp))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (list (make-r1cs-constraint
         :a (list (list 1 x))
         :b (list (list 1 1) (list -1 x))
         :c nil)))

; The correctness (soundness and completeness) of this gadget (family)
; is expressed as follows.
; The hypothesis are boilerplate:
; they say that p is a prime,
; all the variable names (just x here) are symbols,
; asg is an assignment (in alist form) of field elements to variables
; (a 'valuation', in the nomenclature of the formal model of R1CSes),
; and asg binds all the involved variables (just x here).

; The b* binding aids readability of the equality,
; which is the core of the correctness theorem.
; It does not make a big difference in readability for this simple gadget,
; but it does for larger gadgets, as shown later in this file.
; While <var> is a symbol for the variable name,
; <var>$ is a field element, the one that asg assigns to <var>.

; The equality asserts correctness:
; saying that the constraints in the gadget hold
; is like saying that x$ is a bit, i.e. 0 or 1.
; The term (r1cs-constraints-holdp ...) corresponds to
; the relation R in Section 3,
; but using the assignment alist instead of tuples of field elements,
; because r1cs-constraints-holdp is a single predicate,
; and cannot take a varying number of arguments directly.
; In this case, the existentially quantified relation R~ in Section 3
; is the same as R, because the gadget has no internal variables.
; The (bitp ...) term corresponds to
; the specification S in Section 3,
; which is over the only involved field element.
; So this theorem asserts R = S.

; This theorem asserts the correctness of
; the whole family of gadgets captured by boolean-assert-gadget,
; because it is universally quantified over the choice of the variable name.
; It is also universally quantified over the prime p,
; and so this theorem holds for every choice of prime field.

; The proof of this theorem is straightforward.
; Besides obviously enabling the definition of boolean-assert-gadget,
; we enable r1cs-constraint-holdsp and dot-product
; from the formal model of R1CSes
; (note that it is the singular r1cs-constraint-holdsp;
; the plural r1cs-constraints-holdp is handled automatically
; via enabled rules about lists of constraints),
; so that the constraints (just one) directly built by boolean-assert-gadget
; turn into terms involving field elements and operations on them.
; The rules of the prime field library that are locally included in this file
; (see near the beginning of this file)
; suffice to bridge the gap between constraint and specification.

(defruled boolean-assert-gadget-correctness
  (implies (and (primep p)
                (symbolp x)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg x))
           (b* ((x$ (lookup-equal x asg)))
             (equal (r1cs-constraints-holdp (boolean-assert-gadget x) asg p)
                    (bitp x$))))
  :enable (boolean-assert-gadget
           r1cs-constraint-holdsp
           dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the conditional gadget in Figure 2 of the paper.
; It is similar to boolean-assert-gadget above,
; but it is parameterized over four variable names,
; and the constraint is a little more complex.

(define if-then-else-gadget ((w symbolp)
                             (x symbolp)
                             (y symbolp)
                             (z symbolp))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (list (make-r1cs-constraint
         :a (list (list 1 w))
         :b (list (list 1 x) (list -1 y))
         :c (list (list 1 z) (list -1 y)))))

; The correctness theorem is similar to boolean-assert-gadget-correctness,
; but there are four variables involved, along with four bindings,
; and there is also a precondition saying that w$ is boolean (i.e. a bit).
; The precondition is in the inner implication.

; The specification is that z$ is either x$ or y$ based on whether w$ is 1 or 0.
; Like boolean-assert-gadget-correctness,
; this theorem proves R = S, which is the same as R~ = S,
; because this gadget has no internal variables.

(defruled if-then-else-gadget-correctness
  (implies (and (primep p)
                (symbolp w)
                (symbolp x)
                (symbolp y)
                (symbolp z)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg w)
                (valuation-bindsp asg x)
                (valuation-bindsp asg y)
                (valuation-bindsp asg z))
           (b* ((w$ (lookup-equal w asg))
                (x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (bitp w$)
                      (equal (r1cs-constraints-holdp
                              (if-then-else-gadget w x y z) asg p)
                             (equal z$ (if (equal w$ 1) x$ y$))))))
  :enable (if-then-else-gadget
           r1cs-constraint-holdsp
           dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The gadget (family) in Figure 3 is formalized by the following function.
; As the previous ones, it is parameterized over
; the names of all the variables.

; It uses the boolean gadget to build the first constraint,
; while the other two constraints are built directly.
; This showcases some hierarchical structure,
; corresponding to the call graph of the functions.

(define equality-test-gadget ((u symbolp)
                              (v symbolp)
                              (w symbolp)
                              (s symbolp))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (append (boolean-assert-gadget w)
          (list (make-r1cs-constraint
                 :a (list (list 1 u) (list -1 v))
                 :b (list (list 1 s))
                 :c (list (list 1 1) (list -1 w)))
                (make-r1cs-constraint
                 :a (list (list 1 u) (list -1 v))
                 :b (list (list 1 w))
                 :c nil))))

; This gadget has an internal variable, s.
; To highlight the effect of internal variables
; on the soundness and completeness proofs,
; we show separate theorems for soundness and completeness.

; The soundness theorem is similar to the previous correctness theorems,
; starting with the boilerplate hypotheses and then the bindings,
; but the equality R = S is replaced with the implication R ==> S.
; As explained in Section 3,
; the distinction between external and internal variables
; can be ignored as far as soundness is concerned,
; because the existential quantification over the antecedent
; becomes a universal quantification over the implication.
; The antecedent of the (inner) implication mentions s of course,
; but the consequent (the specification) mentions no s$,
; and in fact there is no binding for s$.
; The specification says that
; w$ is 1 or 0 based on whether u$ is equal to v$ or not;
; there is no mention of (the value of) the variable s.

; The proof of this theorem is easy, but it showcases compositionality.
; It uses the correctness theorem for boolean-assert-gadget,
; whose definition is kept disabled in the proof.
; The correcness theorem for boolean-assert-gadget
; rewrites the satisfaction of this sub-gadget of equality-test-gadget
; to the specification bitp.
; Even though boolean-assert-gadget is very simple,
; the same idea applies to sub-gadgets of any complexity:
; they can be turned into their specification
; in proofs for super-gadgets,
; without having the examine their constraints again.

(defruled equality-test-gadget-soundness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (w$ (lookup-equal w asg)))
             (implies (r1cs-constraints-holdp
                       (equality-test-gadget u v w s) asg p)
                      (equal w$ (if (equal u$ v$) 1 0)))))
  :enable (equality-test-gadget
           boolean-assert-gadget-correctness
           r1cs-constraint-holdsp
           dot-product))

; To prove completeness, we can no longer ignore the internal variable.
; The following theorem has a binding for it,
; and r1cs-constraints-holdp is now the consequent of the implication.
; Just using the specification used in the soundness theorem above
; would not work for the completeness theorem:
; the specification just talks about the external variables,
; leaving the internal ones (just s, in this case) free to have any value;
; that cannot guarantee the satisfaction of the constraints.
; Thus, we need to come up with an extended specification S'
; that also involves the internal variable.
; In this case, we can say that either u$ and v$ are equal,
; in which case s$ can be anything,
; or otherwise s$ must be the inverse of the difference of u$ and v$.
; This way, we can prove completeness.
; This theorem proves S' => R.
; The proof is also easy,
; and makes use of the correctness theorem for boolean-assert-gadget,
; as in the soundness theorem.

(defruled equality-test-gadget-completeness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (w$ (lookup-equal w asg))
                (s$ (lookup-equal s asg)))
             (implies (and (equal w$ (if (equal u$ v$) 1 0))
                           (or (equal u$ v$)
                               (equal s$
                                      (inv (sub u$ v$ p)
                                           p))))
                      (r1cs-constraints-holdp
                       (equality-test-gadget u v w s) asg p))))
  :enable (equality-test-gadget
           boolean-assert-gadget-correctness
           r1cs-constraint-holdsp
           dot-product))

; Correctness follows from soundness and completeness,
; but we need to use the extended specification S',
; and we can just prove it directly, using the same hints.
; Note that this has the form R = S', not R~ = S.
; This exposes the details of the internal variables of the gadget.

(defruled equality-test-gadget-correctness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (w$ (lookup-equal w asg))
                (s$ (lookup-equal s asg)))
             (equal (r1cs-constraints-holdp
                     (equality-test-gadget u v w s) asg p)
                    (and (equal w$ (if (equal u$ v$) 1 0))
                         (or (equal u$ v$)
                             (equal s$
                                    (inv (sub u$ v$ p)
                                         p)))))))
  :enable (equality-test-gadget
           boolean-assert-gadget-correctness
           r1cs-constraint-holdsp
           dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Section 2 discusses, in words, the combination of Figure 2 and Figure 3
; to yield a composite gadget.
; This is formalized by the following function,
; which does not build any constraint directly,
; but instead uses two sub-gadgets.
; In this case the arguments passed
; to if-then-else-gadget and equality-test-gadget
; happen to be identical to their formal parameters,
; but that does not need to be the case:
; the name can change, and that is in fact the point of
; parameterizing the constructions over the variable names;
; above, equality-test-gadget calls boolean-assert-gadget
; with a different variable (w) from the formal parameter (x).

; One thing to note is that this combined gadget includes a parameter
; for the internal variable s of equality-test-gadget.
; If this combined gadget is used as sub-gadget of a larger gadget,
; the latter will need a parameter
; for that internal variable of equality-test-gadget.
; The same applies to even larger gadgets,
; i.e. internal variables of gadgets bubble up to all levels.
; This is contrary to modularity,
; and leads to a proliferation of variable name parameters.

(define if-equal-then-else-gadget ((u symbolp)
                                   (v symbolp)
                                   (x symbolp)
                                   (y symbolp)
                                   (z symbolp)
                                   (w symbolp)
                                   (s symbolp))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (append (if-then-else-gadget w x y z)
          (equality-test-gadget u v w s)))

; This combined gadget has two internal variables.
; One is w, used for the condition;
; the other one is s, which bubbles up from equality-test-gadget.
; The specification of the combined gadget is
; in terms of just the external variables (u, v, x, y, z).
; The soundness theorem is analogous to the one of equality-test-gadget:
; there are only bindings for the external variables,
; and the specification only mentions external variables.

; The proof follows from the proofs for the sub-gadgets.
; There is no need to enable r1cs-constraint-holdsp and dot-product
; because this combined gadget does not build any constraints directly.
; For the first sub-gadget,
; we can use the correctness theorem as a rewrite rule.
; For the second gadget,
; we use a :use hint for the soundness theorem,
; to illustrate the point that soundness theorems
; do not work well as rewrite rules, unlike correctness theorems.

(defruled if-equal-then-else-gadget-soundness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg x)
                (valuation-bindsp asg y)
                (valuation-bindsp asg z)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (r1cs-constraints-holdp
                       (if-equal-then-else-gadget u v x y z w s) asg p)
                      (equal z$ (if (equal u$ v$) x$ y$)))))
  :enable (if-equal-then-else-gadget
           if-then-else-gadget-correctness)
  :use equality-test-gadget-soundness)

; To prove completeness, again we need an extended specification S'.
; This has to involve not only the internal variable w,
; which is the proper internal variable of the combined gadget,
; but also the internal variable s of the equality sub-gadget.
; We use the extended specification S' of the equality sub-gadget for both.
; This shows the growth of the extended specification S':
; the completeness proof for any gadget that includes equality-test-gadget
; will always have to talk about its internal variable.

(defruled if-equal-then-else-gadget-completeness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg x)
                (valuation-bindsp asg y)
                (valuation-bindsp asg z)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg))
                (w$ (lookup-equal w asg))
                (s$ (lookup-equal s asg)))
             (implies (and (equal z$ (if (equal u$ v$) x$ y$))
                           (equal w$ (if (equal u$ v$) 1 0))
                           (or (equal u$ v$)
                               (equal s$ (inv (sub u$ v$ p)
                                              p))))
                      (r1cs-constraints-holdp
                       (if-equal-then-else-gadget u v x y z w s) asg p))))
  :enable (if-equal-then-else-gadget
           if-then-else-gadget-correctness)
  :use equality-test-gadget-completeness)

; The correctness theorem of the combined gadget
; is proved easily from the correctness theorems of the sub-gadgets.
; But as in the case of equality-test-gadget,
; it has the form R = S', not R~ = S.

(defruled if-equal-then-else-gadget-correctness
  (implies (and (primep p)
                (symbolp u)
                (symbolp v)
                (symbolp x)
                (symbolp y)
                (symbolp z)
                (symbolp w)
                (symbolp s)
                (r1cs-valuationp asg p)
                (valuation-bindsp asg u)
                (valuation-bindsp asg v)
                (valuation-bindsp asg x)
                (valuation-bindsp asg y)
                (valuation-bindsp asg z)
                (valuation-bindsp asg w)
                (valuation-bindsp asg s))
           (b* ((u$ (lookup-equal u asg))
                (v$ (lookup-equal v asg))
                (x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (r1cs-constraints-holdp
                       (if-equal-then-else-gadget u v x y z w s) asg p)
                      (equal z$ (if (equal u$ v$) x$ y$)))))
  :enable (if-equal-then-else-gadget
           if-then-else-gadget-correctness
           equality-test-gadget-correctness))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Before showing the gadget in Figure 4,
; we need a gadget for lists of boolean constraints of any length.
; This serves to formalize the first n+1 constraints in Figure 4, for generic n.

; The following gadget, unlike the previous ones,
; is parameterized over a list of variable names, of arbitrary length.
; The function recursively builds a list of boolean constraints,
; one per variable, using the single boolean-assert-gadget.
; This gadget is parameterized over the number and names of the variables,
; the number being implicit as the length of the list.
; Note that boolean-assert-gadget is instantiated with different variables.

(define boolean-assert-list-gadget ((xs symbol-listp))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-assert-gadget (car xs))
                   (boolean-assert-list-gadget (cdr xs))))))

; The specification of this gadget is bit-listp.
; That is, the gadget holds iff all the values are bits.
; Note that the boilerplate hypotheses use
; the plural valuation-binds-allp for the list of variables.
; The binding uses lookup-equal-list to bind xs$ to a list of field elements.
; The proof is by induction, and makes use of
; the correctness theorem of boolean-assert-gadget.
; We also need to enable lookup-equal-list,
; but it should be possible to obviate this
; via more rules about lookup-equal-list.

(defruled boolean-assert-list-gadget-correctness
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs-valuationp asg p)
                (valuation-binds-allp asg xs))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (equal (r1cs-constraints-holdp
                     (boolean-assert-list-gadget xs) asg p)
                    (bit-listp xs$))))
  :induct t
  :enable (boolean-assert-list-gadget
           boolean-assert-gadget-correctness
           lookup-equal-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The addition gadget in Figure 4, besides the n+1 boolean gadgets (see above),
; has a constraint that involves power-of-two weighted sums.
; We introduce a function to construct such sums,
; parameterized over the list of variables to use in the sum.

; This function is not quite a gadget constructor,
; but it is a linear combination constructor,
; and linear combinations are constitutents of gadgets.

(define pow2sum-vector ((xs symbol-listp))
  :returns (vec sparse-vectorp :hyp :guard)
  (pow2sum-vector-aux xs 0)
  :prepwork
  ((define pow2sum-vector-aux ((xs symbol-listp) (i natp))
     :returns (vec sparse-vectorp :hyp :guard)
     (cond ((endp xs) nil)
           (t (cons (list (expt 2 i) (car xs))
                    (pow2sum-vector-aux (cdr xs) (1+ i))))))))

; The following is like a correctness theorem for
; the linear combination constructor above.
; It says that evaluating the linear combination (via dot-product)
; with an assignment that includes all the variables
; yields the little endian value of the field elements
; (the function lebits=>nat turns a list of bits
; into their little endian value).
; These field elements are constrained to be bits later,
; but the theorem does not actually need that they are bits.
; The sum is modulo p,
; because the evaluation of the linear combination
; is performed using field operations;
; these can be all turned into integer operations,
; but the final result is modulo p.
; The theorem is proved via a lemma about the recursive auxiliary function,
; which is proved by induction;
; in order to have a sufficiently strong inductive hypothesis,
; the lemma is proved for generic i (the starting power-of-two index),
; which therefore involves multiplication by 2^i.
; This theorem about the linear combination constructor
; is independent from the relation between he prime p and the length of xs;
; the sum is modulo p.

(defruled pow2sum-vector-to-mod-of-lebits=>nat
  (implies (and (primep p)
                (symbol-listp xs)
                (r1cs-valuationp asg p)
                (valuation-binds-allp asg xs))
           (b* ((xs$ (lookup-equal-list xs asg)))
             (implies (bit-listp xs$)
                      (equal (dot-product (pow2sum-vector xs) asg p)
                             (mod (lebits=>nat xs$) p)))))
  :enable (pow2sum-vector fix)
  :prep-lemmas
  ((defrule lemma
     (implies (and (primep p)
                   (symbol-listp xs)
                   (natp i)
                   (r1cs-valuationp asg p)
                   (valuation-binds-allp asg xs))
              (b* ((xs$ (lookup-equal-list xs asg)))
                (implies (bit-listp xs$)
                         (equal (dot-product
                                 (pow2sum-vector-aux xs i) asg p)
                                (mod (* (expt 2 i)
                                        (lebits=>nat xs$))
                                     p)))))
     :induct (pow2sum-vector-aux xs i)
     :enable (pow2sum-vector-aux
              dot-product
              lebits=>nat
              lendian=>nat
              lookup-equal-list
              add
              acl2::expt-of-+
              bitp
              fix))))

; With boolean-assert-list-gadget and pow2sum-vector in hand,
; we can define the addition gadget in Figure 4.
; It is parameterized over the x, y, and z variables, as three lists.
; Both xs and ys have length n, while zs has length n+1.
; The boolean-assert-list-gadget is used to constrain zs to be all bits.
; The constraint about the sums is built directly
; (there are of course a few equivalent ways to fit the desired equality
; <vvalue of xs> + <value of ys> = <value of zs> in the R1CS form).
; The sum of xs and ys is expressed as concatenation of linear combinations.

; This gadget has no internal variables.

(define addition-gadget ((xs symbol-listp)
                         (ys symbol-listp)
                         (zs symbol-listp))
  :guard (and (equal (len ys) (len xs))
              (equal (len zs) (1+ (len xs))))
  :returns (constrs r1cs-constraint-listp :hyp :guard)
  (append (boolean-assert-list-gadget zs)
          (list (make-r1cs-constraint
                 :a (pow2sum-vector zs)
                 :b (list (list 1 1))
                 :c (append (pow2sum-vector xs)
                            (pow2sum-vector ys))))))

; Given the preconditions that xs and ys are bits,
; this gadget is equivalent to the specification:
; the zs are all bits, and their little endian value is
; the sum of the little endian values of xs and ys.
; See the formula in addition-gadget-correctness, at the end of this file.

; The correctness thorem is not hard to prove,
; but takes a little more work than the previous ones.

; In the proof of addition-gadget-correctness at the end of this file,
; we use the theorem for pow2sum-vector proved above,
; which gives us (mod (lebits=>nat ...) p);
; the mod ends up just in two sides of the equation
;   (mod (lebits=>nat ...zs...) p)
;   =
;   (mod (+ (lebits=>nat ...xs...) (lebits=>nat ...ys...)) p)
; which is our desired proof claim, except for the mod.
; But the mod can be eliminated from both sides,
; via the theorems proved below.

; The key point is that both left and right side of the equality
; have n+1 bits, where n = (len xs), which are fewer than the m bits of p.
; That is, n+1 < m (see hypothesis in the theorem),
; so each side is < 2^(n+1), which is therefore <= 2^(m-1),
; but since p has m bits, we have p >= 2^(m-1), and thus p > each side.
; Thus the mod is eliminated, via the arithmetic rules below.

; As explained above,
; if p is a positive integer, and m is its integer length,
; then p is greater than or equal to 2^(m-1),
; because the bit of p at position m-1 must be 1.

(defruledl positive->=-expt2-of-integer-length-minus-1
  (implies (posp p)
           (>= p (expt 2 (1- (integer-length p)))))
  :rule-classes ((:linear :trigger-terms ((integer-length p))))
  :enable (integer-length fix)
  :induct t
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

; We need the monotonicity of expt with base 2.

(defruledl expt2-mono
  (implies (and (natp a)
                (natp b)
                (<= a b))
           (<= (expt 2 a)
               (expt 2 b))))

; That the left side (the one with zs) is < 2^(n+1)
; derives from an enabled linear rule from the digits library,
; which gives an upper bound of lebits=>nat based on the bit length.
; So we do not need any additional theorem here for that.

; For the right side instead we need to derive that bound
; from the bounds of the addends,
; which in turn are derived via the same linear rule as above.
; So here is the theorem we need for the sum.

(defruledl plus-expt2-upper-bound
  (implies (and (integerp n)
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (< (+ a b) (expt 2 (1+ n))))
  :enable fix
  :prep-books ((include-book "arithmetic-3/top" :dir :system)
               (acl2::scatter-exponents)))

; We tie things together for the left side (the one with zs) with this theorem.

(defruledl zs-fits
  (implies (and (posp p)
                (< (len zs) (integer-length p)))
           (< (lebits=>nat zs) p))
  :rule-classes :linear
  :use (:instance expt2-mono
                  (a (len zs))
                  (b (1- (integer-length p))))
  :enable positive->=-expt2-of-integer-length-minus-1
  :disable acl2::<-of-expt-and-expt-same-base)

; We tie things together for the right side with this theorem.

(defruledl xs+ys-fits
  (implies (and (posp p)
                (< (1+ (len xs)) (integer-length p))
                (equal (len ys) (len xs)))
           (< (+ (lebits=>nat xs)
                 (lebits=>nat ys))
              p))
  :rule-classes ((:linear :trigger-terms ((+ (lebits=>nat xs)
                                             (lebits=>nat ys)))))
  :use ((:instance expt2-mono
                   (a (1+ (len xs)))
                   (b (1- (integer-length p))))
        (:instance plus-expt2-upper-bound
                   (n (len xs))
                   (a (lebits=>nat xs))
                   (b (lebits=>nat ys))))
  :enable positive->=-expt2-of-integer-length-minus-1
  :disable acl2::<-of-expt-and-expt-same-base)

; Now we prove the correctness theorem of the gadget.
; We expand addition-gadget, of course, to expose its structure.
; We use boolean-assert-list-gadget-correctness
; to rewrite the boolean constraints to bit-listp for zs.
; We enable r1cs-constraint-holdsp and dot-product
; to handle the directly built constraint;
; the enabled library theorem dot-product-of-append
; handles the concatenation of the linear combinations for xs and ys,
; turning their evaluation into a prime field addition,
; which we enable to turn that into modular integer addition.
; The theorem for pow2sum-vector turns
; (the evaluations of) the linear combination for xs, ys, and zs
; into little endian values modulo p.
; We use the above linear rules to get rid of the modulo p reductions;
; the one for xs+ys somehow does not apply, so we use a :use hint.

(defruled addition-gadget-correctness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len ys) (len xs))
                (equal (len zs) (1+ (len xs)))
                (< (1+ (len xs)) (integer-length p))
                (r1cs-valuationp asg p)
                (valuation-binds-allp asg xs)
                (valuation-binds-allp asg ys)
                (valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs-constraints-holdp
                              (addition-gadget xs ys zs) asg p)
                             (and (bit-listp zs$)
                                  (equal (lebits=>nat zs$)
                                         (+ (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :enable (addition-gadget
           boolean-assert-list-gadget-correctness
           r1cs-constraint-holdsp
           dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           add
           zs-fits)
  :use (:instance xs+ys-fits
                  (xs (lookup-equal-list xs asg))
                  (ys (lookup-equal-list ys asg))))
