; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax-operations")

(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)
(include-book "kestrel/std/util/defund-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "omap-lib-ext"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl symbol-listp-when-symbol-setp
  (implies (symbol-setp x)
           (symbol-listp x))
  :induct t
  :enable symbol-setp)

(defruled sesem-omap-in-to-in-of-keys
  (iff (omap::in key map)
       (set::in key (omap::keys map)))
  :by omap::in-to-in-of-keys)

(defruled sesem-omap-consp-of-in-iff-in
  (iff (consp (omap::in key map))
       (omap::in key map))
  :by omap::consp-of-in-iff-in)

(defruled sesem-natp-of-mod
  (implies (and (natp a)
                (posp b))
           (natp (mod a b))))

(defruled sesem-nfix-when-natp
  (implies (natp x)
           (equal (nfix x) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics-shallowly-embedded
  :parents (semantics)
  :short "Shallowly embedded semantics of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The semantics informally described in @(see semantics)
     can be formalized in a shallowly embedded way,
     by defining ACL2 functions that turn expressions and constraints
     into ACL2 terms and functions that express the semantics.")
   (xdoc::p
    "In the names of the ACL2 functions defined below,
     the prefix @('sesem') stands for `shallowly embedded semantics'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression ((expr expressionp) (prime symbolp))
  :returns term
  :short "Shallowly embedded semantics of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the expression, this function also takes as argument
     a variable (symbol) to use as the prime.
     This is needed because we generate terms involving prime field operations,
     which all take a prime as argument;
     the prime is also used to reduce integer constants.")
   (xdoc::p
    "A constant is mapped to itself, reduced modulo the prime.")
   (xdoc::p
    "A variable is mapped to itself,
     but we ensure that it is distinct from the prime variable;
     otherwise, we would be generating a malformed term.")
   (xdoc::p
    "Additions and multiplications are mapped to calls of
     the corresponding prime field operations applied to
     the terms obtained by translating the argument expressions."))
  (expression-case
   expr
   :const `(mod ,expr.value ,prime)
   :var (if (eq expr.name prime)
            (raise "The expression variable ~x0 ~
                    is identical to ~
                    the prime variable ~x1."
                   expr.name prime)
          expr.name)
   :add `(add ,(sesem-expression expr.arg1 prime)
              ,(sesem-expression expr.arg2 prime)
              ,prime)
   :mul `(mul ,(sesem-expression expr.arg1 prime)
              ,(sesem-expression expr.arg2 prime)
              ,prime))
  :measure (expression-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression-list ((exprs expression-listp) (prime symbolp))
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of lists of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-expression) to lists.
     We obtain a list of terms."))
  (cond ((endp exprs) nil)
        (t (cons (sesem-expression (car exprs) prime)
                 (sesem-expression-list (cdr exprs) prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint ((constr constraintp) (prime symbolp))
  :returns term
  :short "Shallowly embedded semantics of a constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn an equality constraint into an ACL2 equality
     of the terms denoted by the left and right expressions.
     We turn a relation constraint into an ACL2 call of the relation
     on the terms denoted by the argument expressions.
     Note that we include the variable for the prime."))
  (constraint-case
   constr
   :equal `(equal ,(sesem-expression constr.left prime)
                  ,(sesem-expression constr.right prime))
   :relation `(,constr.name ,@(sesem-expression-list constr.args prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint-list ((constrs constraint-listp) (prime symbolp))
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of a list of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-constraint) to lists.
     We obtain a list of terms."))
  (cond ((endp constrs) nil)
        (t (cons (sesem-constraint (car constrs) prime)
                 (sesem-constraint-list (cdr constrs) prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-gen-fep-terms ((vars symbol-listp) (prime symbolp))
  :returns (terms pseudo-term-listp :hyp :guard)
  :short "Generate a list of terms @('(fep x1 p)'), ..., @('(fep xn p)')
          from a list of variables @('x1'), ..., @('xn')."
  (cond ((endp vars) nil)
        (t (cons `(fep ,(car vars) ,prime)
                 (sesem-gen-fep-terms (cdr vars) prime))))
  :prepwork ((local (in-theory (enable pseudo-termp pseudo-term-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition ((def definitionp) (prime symbolp))
  :returns (event pseudo-event-formp)
  :short "Shallowly embedded semantics of a definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We turn the definition into an ACL2 function definition
     that defines a predicate that holds exactly on the values
     that satisfy all the constraints.
     If the definition has no free variables,
     we generate a @(tsee defun).
     Otherwise, we generate a @(tsee defun-sk)
     with those free variables existentially quantified.
     (More precisely, we generate @(tsee defund) or @tsee defund-sk).")
   (xdoc::p
    "The existential quantification is the right semantics
     for the free variables in a relation's definition,
     based on the intended use of these constraints in zero-knowledge proofs.
     However, the quantification is avoided
     if all the variables in the body are treated as parameters."))
  (b* (((definition def) def)
       ((when (member-eq prime def.para))
        (raise "The definition parameters ~x0 of ~x1 ~
                include the prime variable ~x2."
               def.para def.name prime)
        '(_))
       (free (definition-free-vars def))
       ((when (set::in prime free))
        (raise "The free variables ~x0 of ~x1 ~
                include the prime variable ~x2."
               free def.name prime)
        '(_))
       (body `(and ,@(sesem-constraint-list def.body prime))))
    (if free
        `(defund-sk ,def.name (,@def.para ,prime)
           (exists (,@free) (and ,@(sesem-gen-fep-terms free prime) ,body)))
      `(defund ,def.name (,@def.para ,prime)
         ,body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition-list ((defs definition-listp) (prime symbolp))
  :returns (events pseudo-event-form-listp)
  :short "Shallowly embedded semanics of a list of definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of events generated from the definitions."))
  (cond ((endp defs) nil)
        (t (cons (sesem-definition (car defs) prime)
                 (sesem-definition-list (cdr defs) prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition-thm ((def definitionp) (prime symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate theorem connecting deeply and shallowly embedded semantics,
          for PFCS definitions without free variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a PFCS definition,
     @(tsee sesem-definition) generates a shallowly embedded version of it.
     Here we define a theorem connecting that shallowly embedded version
     to the deeply embedded semantics of the definition.")
   (xdoc::p
    "The theorem says that
     the satisfaction of the definition (expressed via @(tsee definition-satp)
     is equivalent to the satisfaction of the shallowly embedded definition.")
   (xdoc::p
    "When the definition has no free variables,
     the theorem is proved by enabling certain definitions and rules.
     The proof is obtained completely by rewriting.")
   (xdoc::p
    "If the definition has free variables,
     the shallowly embedded version of the definition is a @(tsee defun-sk),
     as is @(tsee constraint-relation-satp);
     the latter is what @(tsee definition-satp) gets rewritten to,
     using the rules passed to the proof.
     Both @(tsee defun-sk)s are existentially quantified.
     Essentially, we need to show that each one implies the other,
     using the witness of one to calculate the witness of the other.
     The proof naturally splits into two parts (`only if' and `if').
     Each part if proved mostly by rewriting,
     but we also need some lemma instances.
     The lemma instances for the @('suff') rules of the @(tsee defun-sk)s
     are expected.
     The other instances serve to establish that
     the parameters are not in @('asgfree')
     while the existentially quantified variables are in @('asgfree'):
     we need to leverage the relation between @(tsee omap::in)
     and set membership in @(tsee omap::keys),
     given things are formulated;
     perhaps there is a way to do this via rewrite rules."))

  (b* (((definition def) def)
       (free (definition-free-vars def))
       (thm-name (acl2::packn-pos (list 'definition-satp-of-
                                        def.name
                                        '-to-shallow)
                                  def.name))

       ((when (equal free nil))
        `(defruled ,thm-name
           (implies (and (equal (lookup-definition ',def.name defs)
                                ',def)
                         ,@(sesem-gen-fep-terms def.para prime))
                    (equal (definition-satp
                             ',def.name defs (list ,@def.para) ,prime)
                           (,def.name ,@def.para ,prime)))
           :in-theory '(,def.name
                        (:e ,def.name)
                        definition-satp
                        constraint-satp-of-relation-when-nofreevars
                        constraint-relation-nofreevars-satp
                        constraint-list-satp-of-cons
                        constraint-list-satp-of-nil
                        constraint-satp-of-equal
                        constraint-equal-satp
                        eval-expr
                        eval-expr-list
                        (:e definition->para)
                        (:e definition->body)
                        (:e definition-free-vars)
                        (:e constraint-kind)
                        (:e constraint-equal->left)
                        (:e constraint-equal->right)
                        (:e constraint-relation)
                        (:e constraint-relation->name)
                        (:e constraint-relation->args)
                        (:e expression-kind)
                        (:e expression-const->value)
                        (:e expression-var->name)
                        (:e expression-add->arg1)
                        (:e expression-add->arg2)
                        (:e expression-mul->arg1)
                        (:e expression-mul->arg2)
                        (:e expression-var-list)
                        assignment-wfp-of-update
                        assignment-wfp-of-nil
                        assignment-fix-when-assignmentp
                        assignmentp-of-update
                        (:e assignmentp)
                        omap::from-lists
                        pfield::fep-fw-to-natp
                        pfield::natp-of-add
                        pfield::natp-of-mul
                        len
                        fty::consp-when-reserrp
                        acl2::natp-compound-recognizer
                        (:e nat-listp)
                        (:e set::empty)
                        car-cons
                        cdr-cons
                        omap::in-of-update
                        acl2::nat-listp-of-cons
                        acl2::not-reserrp-when-nat-listp
                        nfix
                        (:t mod))))

       (constraint-relation-satp-witness
        `(constraint-relation-satp-witness ',def.name
                                           ',(expression-var-list def.para)
                                           defs
                                           (omap::from-lists ',def.para
                                                             (list ,@def.para))
                                           ,prime))
       (def-witness `(,(add-suffix-to-fn def.name "-WITNESS")
                      ,@def.para ,prime)))

    `(defruled ,thm-name
       (implies (and (equal (lookup-definition ',def.name defs)
                            ',def)
                     ,@(sesem-gen-fep-terms def.para prime)
                     (posp ,prime))
                (equal (definition-satp
                         ',def.name defs (list ,@def.para) ,prime)
                       (,def.name ,@def.para ,prime)))
       :in-theory '((:t definition-satp)
                    (:t ,def.name))
       :use (only-if-direction if-direction)

       :prep-lemmas

       ((defruled only-if-direction
          (implies (and (equal (lookup-definition ',def.name defs)
                               ',def)
                        ,@(sesem-gen-fep-terms def.para prime))
                   (implies (definition-satp
                              ',def.name defs (list ,@def.para) ,prime)
                            (,def.name ,@def.para ,prime)))
          :in-theory '(definition-satp
                        constraint-satp-of-relation
                        constraint-relation-satp
                        constraint-list-satp-of-cons
                        constraint-list-satp-of-nil
                        constraint-satp-of-equal
                        constraint-equal-satp
                        eval-expr
                        eval-expr-list
                        (:e definition->para)
                        (:e definition->body)
                        (:e definition-free-vars)
                        (:e constraint-kind)
                        (:e constraint-equal->left)
                        (:e constraint-equal->right)
                        (:e constraint-relation)
                        (:e constraint-relation->name)
                        (:e constraint-relation->args)
                        (:e expression-kind)
                        (:e expression-const->value)
                        (:e expression-var->name)
                        (:e expression-add->arg1)
                        (:e expression-add->arg2)
                        (:e expression-mul->arg1)
                        (:e expression-mul->arg2)
                        (:e expression-var-list)
                        assignment-wfp-of-update*
                        assignment-wfp-of-update
                        assignment-wfp-of-nil
                        assignment-fix-when-assignmentp
                        assignmentp-of-update*
                        assignmentp-of-update
                        (:e assignmentp)
                        omap::from-lists
                        pfield::fep-fw-to-natp
                        pfield::natp-of-add
                        pfield::natp-of-mul
                        len
                        fty::consp-when-reserrp
                        acl2::natp-compound-recognizer
                        (:e nat-listp)
                        (:e set::empty)
                        car-cons
                        cdr-cons
                        omap::in-of-update*
                        omap::in-of-update
                        acl2::nat-listp-of-cons
                        acl2::not-reserrp-when-nat-listp
                        sesem-nfix-when-natp
                        (:t mod)
                        (:t reserr)
                        fty::reserrp-of-reserr
                        sesem-omap-consp-of-in-iff-in
                        (:e set::in)
                        natp-of-cdr-of-in-when-assignmentp-type
                        fep-of-cdr-of-in-when-assignment-wfp)
          :use ((:instance ,(add-suffix-to-fn def.name "-SUFF")
                           ,@(sesem-definition-thm-aux1
                              free constraint-relation-satp-witness))
                ,@(sesem-definition-thm-aux2
                   (append def.para free)
                   constraint-relation-satp-witness)))

        (defruled if-direction
          (implies (and (equal (lookup-definition ',def.name defs)
                               ',def)
                        ,@(sesem-gen-fep-terms def.para prime)
                        (posp ,prime))
                   (implies (,def.name ,@def.para ,prime)
                            (definition-satp
                              ',def.name defs (list ,@def.para) ,prime)))
          :in-theory '(,def.name
                       definition-satp
                       constraint-satp-of-relation
                       constraint-list-satp-of-cons
                       constraint-list-satp-of-nil
                       constraint-satp-of-equal
                       constraint-equal-satp
                       eval-expr
                       eval-expr-list
                       (:e definition->para)
                       (:e definition->body)
                       (:e definition-free-vars)
                       (:e constraint-kind)
                       (:e constraint-equal->left)
                       (:e constraint-equal->right)
                       (:e constraint-relation)
                       (:e constraint-relation->name)
                       (:e constraint-relation->args)
                       (:e expression-kind)
                       (:e expression-const->value)
                       (:e expression-var->name)
                       (:e expression-add->arg1)
                       (:e expression-add->arg2)
                       (:e expression-mul->arg1)
                       (:e expression-mul->arg2)
                       (:e expression-var-list)
                       assignment-wfp-of-update*
                       assignment-wfp-of-update
                       assignment-wfp-of-nil
                       assignment-fix-when-assignmentp
                       assignmentp-of-update*
                       assignmentp-of-update
                       (:e assignmentp)
                       omap::from-lists
                       pfield::fep-fw-to-natp
                       car-cons
                       cdr-cons
                       (:e nat-listp)
                       omap::keys-of-update
                       omap::in-of-update*
                       omap::in-of-update
                       (:e omap::keys)
                       (:e set::insert)
                       len
                       sesem-nfix-when-natp
                       (:e reserrp)
                       acl2::not-reserrp-when-natp
                       nat-listp
                       (:e omap::in)
                       sesem-natp-of-mod
                       (:e natp))
          :use (:instance constraint-relation-satp-suff
                          (asgfree (omap::from-lists
                                    ',free
                                    (list ,@(sesem-definition-thm-aux3
                                             free def-witness))))
                          (name ',def.name)
                          (args (expression-var-list ',def.para))
                          (asg (omap::from-lists ',def.para
                                                 (list ,@def.para))))))))

  :prepwork

  ((define sesem-definition-thm-aux1 ((free symbol-listp) (witness "A term."))
     :returns (doublets doublet-listp)
     (cond ((endp free) nil)
           (t (cons `(,(car free)
                      (cdr (omap::in ',(car free) ,witness)))
                    (sesem-definition-thm-aux1 (cdr free) witness))))
     :prepwork ((local (in-theory (enable doublet-listp length len)))))

   (define sesem-definition-thm-aux2 ((vars symbol-listp) (witness "A term."))
     :returns (lemma-instances true-listp)
     (cond ((endp vars) nil)
           (t (cons `(:instance sesem-omap-in-to-in-of-keys
                                (key ',(car vars))
                                (map ,witness))
                    (sesem-definition-thm-aux2 (cdr vars) witness)))))

   (define sesem-definition-thm-aux3 ((free symbol-listp) (witness "A term."))
     :returns (terms true-listp)
     (cond ((endp free) (raise "Error."))
           ((endp (cdr free)) (list witness))
           (t (sesem-definition-thm-aux3-aux free 0 witness)))
     :prepwork
     ((define sesem-definition-thm-aux3-aux ((free symbol-listp)
                                             (index natp)
                                             (witness "A term."))
        :returns (terms true-listp)
        (cond ((endp free) nil)
              (t (cons `(mv-nth ,index ,witness)
                       (sesem-definition-thm-aux3-aux
                        (cdr free) (1+ index) witness)))))))))
