; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-trees")
(include-book "r1cs-subset")

(include-book "r1cs-lib-ext")

(include-book "std/util/defprojection" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ r1cs-bridge
  :parents (pfcs)
  :short "Bridge between PFCSes and R1CSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCSes are a generalization of R1CSes.
     Thus, there is an embedding of R1CSes into PFCSes,
     which we reify by providing a mapping from R1CSes to PFCSes.")
   (xdoc::p
    "The mapping functions are accompanied by theorems
     showing that the resulting PFCSes are in the "
    (xdoc::seetopic "r1cs-subset" "R1CS subset")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-vec-elem-to-pfcs (elem)
  :guard (and (true-listp elem)
              (equal (len elem) 2)
              (integerp (first elem))
              (r1cs::pseudo-varp (second elem)))
  :returns (expr expressionp)
  :short "Translate an R1CS vector element to a PFCS expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "An element of an R1CS (sparse) vector is
     a list of two elements:
     an integer coefficient and a pseudo-variable.
     If the pseudo-variable is 1, we generate a constant with the coefficient.
     Otherwise, if the coefficient is 1 and the pseudo-variable is a symbol,
     we generate a variable with the name of the symbol.
     Otherwise, we generate a multiplication
     of the coefficient by the variable.")
   (xdoc::p
    "This mapping works if the R1CS variables have distinct symbol names.
     Otherwise, different R1CS variables could become the same PFCS variable.
     We plan to make this mapping more robust at some point."))
  (b* ((coeff (first elem))
       (pvar (second elem)))
    (cond ((equal pvar 1) (expression-const coeff))
          ((equal coeff 1) (expression-var (symbol-name pvar)))
          (t (make-expression-mul :arg1 (expression-const (first elem))
                                  :arg2 (expression-var (symbol-name pvar))))))
  ///

  (more-returns
   (expr r1cs-monomialp
         :hints (("Goal" :in-theory (enable r1cs-monomialp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-vector-to-pfcs ((vec r1cs::sparse-vectorp))
  :returns (expr expressionp)
  :short "Translate an R1CS (sparse) vector to a PFCS expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We translate the empty vector to the PFCS constant 0.
     We translate a singleton vector to
     the element's corresponding PFCS expression.
     We translate vectors of two or more elements
     to (nested) PFCS additions;
     these are nested to the left,
     so we reverse the vector before the recursion."))
  (r1cs-vector-to-pfcs-aux (rev vec))

  :prepwork
  ((define r1cs-vector-to-pfcs-aux ((rev-vec r1cs::sparse-vectorp))
     :returns (expr expressionp)
     :parents nil
     (cond ((endp rev-vec) (expression-const 0))
           ((endp (cdr rev-vec)) (r1cs-vec-elem-to-pfcs (car rev-vec)))
           (t (make-expression-add
               :arg1 (r1cs-vector-to-pfcs-aux (cdr rev-vec))
               :arg2 (r1cs-vec-elem-to-pfcs (car rev-vec)))))
     :verify-guards :after-returns
     ///
     (more-returns
      (expr r1cs-polynomialp
            :hints (("Goal" :induct t :in-theory (enable r1cs-polynomialp)))))))

  ///

  (more-returns
   (expr r1cs-polynomialp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-constraint-to-pfcs ((rconstr r1cs::r1cs-constraintp))
  :returns (pconstr constraintp)
  :short "Translate an R1CS constraint to a PFCS constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "We translate this to an equality constraint between
     (i) the product of @('a') and @('b') and (ii) @('c')."))
  (b* ((a-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->a rconstr)))
       (b-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->b rconstr)))
       (c-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->c rconstr))))
    (make-constraint-equal
     :left (make-expression-mul :arg1 a-expr :arg2 b-expr)
     :right c-expr))
  ///

  (more-returns
   (pconstr r1cs-constraintp
            :hints (("Goal" :in-theory (enable r1cs-constraintp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection r1cs-constraints-to-pfcs (x)
  :guard (r1cs::r1cs-constraint-listp x)
  :returns (pconstrs constraint-listp)
  :short "Translate a list of R1CS constraints to a list of PFCS constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are translated element-wise."))
  (r1cs-constraint-to-pfcs x)
  ///

  (more-returns
   (pconstrs r1cs-constraint-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-to-pfcs ((r1cs r1cs::r1csp))
  :returns (sys systemp)
  :short "Translate an R1CS to a PFCS."
  :long
  (xdoc::topstring
   (xdoc::p
    "An R!CS is formalized as consisting of
     a prime, a list of variables, and a list of constraints.
     We translate this to a PFCS with no definitions
     and whose constraints are the ones of the R1CS (translated).
     We ignore the prime in the R1CS,
     because PFCSes do not include primes, syntactically."))
  (make-system :definitions nil
               :constraints (r1cs-constraints-to-pfcs
                             (r1cs::r1cs->constraints r1cs)))
  ///

  (more-returns
   (sys r1cs-systemp
        :hints (("Goal" :in-theory (enable r1cs-systemp))))))
