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

(include-book "proof-support")

(include-book "std/strings/char-case" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)
(include-book "std/system/table-alist-plus" :dir :system)
(include-book "std/util/defund-sk" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/union" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lifting
  :parents (pfcs)
  :short "Lifting of PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "The semantics informally described in @(see semantics)
     can be also formalized in a shallowly embedded way,
     by defining ACL2 functions that turn
     (abstract syntax of) expressions and constraints
     into ACL2 terms and functions that express the semantics.
     This amounts to lifting deeply embedded PFCSes
     into a shallowly embedded representation of them.")
   (xdoc::p
    "Here we define these ACL2 functions,
     whose prefix @('sesem') stands for `shallowly embedded semantics'.
     We also provide an event macro to turn
     a deeply embedded PFCS definition
     to a shallowly embedded version of it,
     also generating a theorem that relates the two.
     The theorem says that
     the satisfaction of the deeply embedded definition
     is equivalent to the satisfaction of the shallowly embedded one."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define current-package+ (state)
  :returns (package stringp)
  :short "Logic-friendly wrapper of the built-in @(tsee current-package)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This belongs to a more general library."))
  (b* ((package (current-package state))
       ((unless (and (stringp package)
                     (not (equal package ""))))
        (raise "Internal error: current package ~x0 is not a string." package)
        "."))
    package)
  ///

  (defret current-package+-not-empty
    (not (equal package ""))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-to-symbol ((name stringp) state)
  :returns (sym symbolp)
  :short "Turn a PFCS relation or variable name into an ACL2 symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "The PFCS abstract syntax uses strings for relation and variable names.
     These must be turned into symbols in the shallowly embedded semantics.
     Here we define the mapping.")
   (xdoc::p
    "Assuming that PFCS relation and variable names
     would normally consist of lowercase letters, digits, and underscores,
     we map lowercase letters to uppercase letters,
     digits to themselves,
     and underscores to dashes;
     we use the resulting string as name of the symbol,
     which we put in the current package.
     This way, idiomatic PFCS names are mapped to idiomatic ACL2 symbols.")
   (xdoc::p
    "This mapping is not bulletproof.
     The current package may import symbols from the Lisp package, for example,
     and a PFCS name may end up being mapped to a symbol in the Lisp package,
     which cannot be used as an ACL2 name.
     In the future, we may make this mapping more robust."))
  (b* ((chars (str::explode name))
       (new-chars (name-to-symbol-aux chars))
       (new-string (str::implode new-chars)))
    (intern$ new-string (current-package+ state)))

  :prepwork
  ((define name-to-symbol-aux ((chars character-listp))
     :returns (new-chars character-listp)
     :parents nil
     (b* (((when (endp chars)) nil)
          (char (car chars))
          (new-char (if (equal char #\_)
                        #\-
                      (str::upcase-char char)))
          (new-chars (name-to-symbol-aux (cdr chars))))
       (cons new-char new-chars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection name-list-to-symbol-list (x state)
  :guard (string-listp x)
  :returns (symbols symbol-listp)
  :short "Turn a list of PFCS relation or variable names
          into a list of ACL2 symbols."
  (name-to-symbol x state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define name-set-to-symbol-list ((names string-setp) state)
  :returns (syms symbol-listp)
  :short "Lift @(tsee name-to-symbol) to a mapping
          from sets of strings to lists of symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "The order of the list is according to
     the total order that osets are based on."))
  (cond ((set::emptyp names) nil)
        (t (cons (name-to-symbol (set::head names) state)
                 (name-set-to-symbol-list (set::tail names) state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression ((expr expressionp) (prime symbolp) state)
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
    "A variable is mapped to a symbol, according to @(tsee name-to-symbol).")
   (xdoc::p
    "Additions and multiplications are mapped to calls of
     the corresponding prime field operations applied to
     the terms obtained by translating the argument expressions."))
  (expression-case
   expr
   :const `(mod ,expr.value ,prime)
   :var (name-to-symbol expr.name state)
   :add `(add ,(sesem-expression expr.arg1 prime state)
              ,(sesem-expression expr.arg2 prime state)
              ,prime)
   :mul `(mul ,(sesem-expression expr.arg1 prime state)
              ,(sesem-expression expr.arg2 prime state)
              ,prime))
  :measure (expression-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-expression-list ((exprs expression-listp) (prime symbolp) state)
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of lists of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-expression) to lists.
     We obtain a list of terms."))
  (cond ((endp exprs) nil)
        (t (cons (sesem-expression (car exprs) prime state)
                 (sesem-expression-list (cdr exprs) prime state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint ((constr constraintp) (prime symbolp) state)
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
   :equal `(equal ,(sesem-expression constr.left prime state)
                  ,(sesem-expression constr.right prime state))
   :relation `(,(name-to-symbol constr.name state)
               ,@(sesem-expression-list constr.args prime state)
               ,prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-constraint-list ((constrs constraint-listp) (prime symbolp) state)
  :returns (terms true-listp)
  :short "Shallowly embedded semantics of a list of constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee sesem-constraint) to lists.
     We obtain a list of terms."))
  (cond ((endp constrs) nil)
        (t (cons (sesem-constraint (car constrs) prime state)
                 (sesem-constraint-list (cdr constrs) prime state)))))

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

(define sesem-definition ((def definitionp) (prime symbolp) state)
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
     (More precisely, we generate @(tsee defund) or @(tsee defund-sk)).")
   (xdoc::p
    "The existential quantification is the right semantics
     for the free variables in a relation's definition,
     based on the intended use of these constraints in zero-knowledge proofs.
     However, the quantification is avoided
     if all the variables in the body are treated as parameters."))
  (b* (((definition def) def)
       (pred-name (name-to-symbol def.name state))
       (free (definition-free-vars def))
       (quant (name-set-to-symbol-list free state))
       (para (name-list-to-symbol-list def.para state))
       (body `(and ,@(sesem-constraint-list def.body prime state))))
    (if free
        `(defund-sk ,pred-name (,@para ,prime)
           (exists (,@quant) (and ,@(sesem-gen-fep-terms quant prime) ,body)))
      `(defund ,pred-name (,@para ,prime)
         ,body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition-list ((defs definition-listp) (prime symbolp) state)
  :returns (events pseudo-event-form-listp)
  :short "Shallowly embedded semanics of a list of definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of events generated from the definitions."))
  (cond ((endp defs) nil)
        (t (cons (sesem-definition (car defs) prime state)
                 (sesem-definition-list (cdr defs) prime state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lift-rules
  :short "Some rules used by the lifter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lifter generates proofs that make use of
     certain rules about omaps and about some built-ins.
     To avoid a dependency on the libraries that contain those rules,
     here we create versions of these rules that are part of the lifter
     and that are used in proofs generated by the lifter."))

  (defruled lift-rule-omap-in-to-in-of-keys
    (iff (omap::assoc key map)
         (set::in key (omap::keys map)))
    :by omap::assoc-to-in-of-keys)

  (defruled lift-rule-omap-consp-of-assoc-iff-assoc
    (iff (consp (omap::assoc key map))
         (omap::assoc key map))
    :by omap::consp-of-assoc-iff-assoc)

  (defruled lift-rule-natp-of-mod
    (implies (and (integerp a)
                  (posp b))
             (natp (mod a b))))

  (defruled lift-rule-nfix-when-natp
    (implies (natp x)
             (equal (nfix x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod lift-info
  :short "Fixtype of information about lifted PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are stored in the @(see lift-table).
     For each lifted PFCS definition,
     we store the abstract syntax of the definition
     and a list of terms used as hypotheses in generated theorems.
     Each term in the list says that
     looking up a certain PFCS definition by name
     yields the expected abstract syntax of the definition;
     there is one such term
     for the PFCS definition that this information refers to,
     and one such term for each PFCS definition
     directly or indirectly called by
     the PFCS definition that this information refers to."))
  ((def definition)
   (hyps true-list))
  :pred lift-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lift-table
  :short "Table of information about lifted PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each lifted PFCS definition,
     we store an entry in this table
     whose key is the definition name (a string)
     and whose value is the information of type @(tsee lift-info)."))

  (table lift-table nil nil
    :guard (and (stringp acl2::key)
                (lift-infop acl2::val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-def-hyps ((def definitionp) (wrld plist-worldp))
  :returns (hyps true-listp)
  :short "Hypotheses about certain relations having the expected definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are hypotheses in the generated lifting theorems.
     For each relation,
     whose definition is the @('def') parameter passed to this function,
     we need the hypothesis that looking up the relation in @('defs')
     (which is the variable, in the generated theorem,
     holding the definitions with respect to which the semntics is given)
     yields @('def').
     We also need the cumulative hypotheses of the same form
     of the relations called directly or indirectly by @('def'):
     these are retrieved from the table of lifted PFCSes,
     taking the set-like union (thus avoiding duplicates)
     of each relation called."))
  (b* (((definition def) def)
       (hyp `(equal (lookup-definition ,def.name defs) ',def))
       (crels (constraint-list-constrels def.body))
       (tab (table-alist+ 'lift-table wrld))
       (more-hyps (lift-thm-def-hyps-aux crels tab)))
    (cons hyp more-hyps))

  :prepwork
  ((define lift-thm-def-hyps-aux ((crels constrel-setp) (tab alistp))
     :returns (more-hyps true-listp)
     :parents nil
     (b* (((when (set::emptyp crels)) nil)
          (crel (set::head crels))
          (name (constrel->name crel))
          (info (cdr (assoc-equal name tab)))
          ((unless info)
           (raise "Internal error: ~x0 not in table." name))
          ((unless (lift-infop info))
           (raise "Internal error: ~x0 has the wrong type." info))
          (hyps (lift-info->hyps info))
          (more-hyps (lift-thm-def-hyps-aux (set::tail crels) tab)))
       (union-equal hyps more-hyps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-free-inst ((free string-setp) (witness "A term.") state)
  :returns (doublets doublet-listp)
  :short "Calculate an instantiation of free variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to prove the lifting theorem,
     precisely the `only if' direction of the theorem
     for the case in which the relation has free variables.
     This instantiation is used in a lemma instance (see @(tsee lift-thm)).
     The instantiation replaces each variable
     with its lookup in the witness term of the @(tsee defun-sk)."))
  (cond ((set::emptyp free) nil)
        (t (b* ((var (set::head free)))
             (cons `(,(name-to-symbol var state)
                     (cdr (omap::assoc ,var ,witness)))
                   (lift-thm-free-inst (set::tail free) witness state)))))
  :prepwork ((local (in-theory (enable doublet-listp length len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-omap-keys-lemma-instances ((vars string-listp)
                                            (witness "A term."))
  :returns (lemma-instances true-listp)
  :short "Calculate lemmas instances for the lifting theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate one lemma instance for each variable passed as input.
     The lemma is the same for all instances."))
  (cond ((endp vars) nil)
        (t (cons `(:instance lift-rule-omap-in-to-in-of-keys
                             (key ,(car vars))
                             (map ,witness))
                 (lift-thm-omap-keys-lemma-instances (cdr vars) witness)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-asgfree-pairs ((quant symbol-listp) (witness "A term."))
  :returns (terms true-listp)
  :short "Calculate a list of pairs for constructing
          a witness assignment to quantified variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used in the hints for the `if' direction of the lifting theorem,
     when there are free PFCS variables,
     which become quantified variables in ACL2."))
  (cond ((endp quant) (raise "Error."))
        ((endp (cdr quant)) (list witness))
        (t (lift-thm-asgfree-pairs-aux quant 0 witness)))

  :prepwork
  ((define lift-thm-asgfree-pairs-aux ((quant symbol-listp)
                                       (index natp)
                                       (witness "A term."))
     :returns (terms true-listp)
     (cond ((endp quant) nil)
           (t (cons `(mv-nth ,index ,witness)
                    (lift-thm-asgfree-pairs-aux
                     (cdr quant) (1+ index) witness)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-called-lift-thms ((rels symbol-listp))
  :returns (called-lift-thms)
  :short "List of lifting theorems for a set of relations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as rewrite rules in the caller's lifting theorem."))
  (b* (((when (endp rels)) nil)
       (rel (car rels)))
    (cons (acl2::packn-pos (list 'definition-satp-of- rel '-to-shallow) rel)
          (lift-thm-called-lift-thms (cdr rels)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-definition-satp-specialized-lemma ((def definitionp) state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp))
  :short "Generate a local lemma to apply
          the definition of @(tsee definition-satp)
          to a specific definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "To prove the lifting theorem,
     we need to open @(tsee definition-satp)
     when applied to the name of the definition @('def') that we are lifting.
     If @('def') calls other definitions,
     in the course of the proof there will be
     other instances of @(tsee definition-satp)
     applied to the names of the called definitions.
     For these, @(tsee definition-satp) must not be opened,
     because we need to use the lifting theorems for those definitions.
     Thus, just enabling @(tsee definition-satp) is too coarse.
     In order to limit the application of this ACL2 definition,
     we generate a local lemma which is
     essentially the definition of @(tsee definition-satp)
     specialized to the name of the definition to be the one of @('def')."))
  (b* ((def-name (definition->name def))
       (pred-name (name-to-symbol def-name state))
       (thm-name (acl2::packn-pos (list 'definition-satp-of- pred-name)
                                  pred-name))
       (thm-event
        `(defruledl ,thm-name
           (equal (definition-satp ,def-name defs vals p)
                  (b* ((def (lookup-definition ,def-name defs))
                       ((unless def) nil)
                       (para (definition->para def))
                       ((unless (equal (len vals) (len para))) nil)
                       (asg (omap::from-lists para vals))
                       (constr (make-constraint-relation
                                :name ,def-name
                                :args (expression-var-list para))))
                    (constraint-satp constr defs asg p)))
           :in-theory '(definition-satp))))
    (mv thm-event thm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-constr-satp-specialized-lemma ((def definitionp) state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp))
  :short "Generate a local lemma to apply
          @(tsee constraint-satp-of-relation) or
          @(tsee constraint-satp-of-relation-when-nofreevars)
          to a specific relation constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous in purpose to
     @(tsee lift-thm-definition-satp-specialized-lemma),
     but for a different rule:
     the choice between the two aforementioned rules is determined
     by whether the definition @('def') has free variables or not.
     In the lifting theorem,
     we need to apply this rule to the constraint obtained
     by opening @(tsee definition-satp) on @('def'),
     but not on the constraints for any relations called by @('def'),
     because for those we want to apply a different rule.
     So the local lemma that we generate here limits application
     to the constraint with the name of @('def')."))
  (b* ((def-name (definition->name def))
       (pred-name (name-to-symbol def-name state))
       (thm-name (acl2::packn-pos (list 'constraint-satp-of- pred-name)
                                  pred-name))
       (thm-event
        (if (set::emptyp (definition-free-vars def))
            `(defruledl ,thm-name
               (implies (and (assignmentp asg)
                             (assignment-wfp asg p)
                             (constraint-case constr :relation)
                             (equal (constraint-relation->name constr)
                                    ,def-name))
                        (b* ((args (constraint-relation->args constr))
                             (def (lookup-definition ,def-name defs)))
                          (implies (and def
                                        (set::emptyp (definition-free-vars def)))
                                   (equal (constraint-satp constr defs asg p)
                                          (constraint-relation-nofreevars-satp
                                           ,def-name args defs asg p)))))
               :in-theory '(constraint-satp-of-relation-when-nofreevars))
          `(defruledl ,thm-name
             (implies (and (assignmentp asg)
                           (assignment-wfp asg p)
                           (constraint-case constr :relation)
                           (equal (constraint-relation->name constr)
                                  ,def-name))
                      (equal (constraint-satp constr defs asg p)
                             (constraint-relation-satp
                              ,def-name
                              (constraint-relation->args constr)
                              defs
                              asg
                              p)))
             :in-theory '(constraint-satp-of-relation)))))
    (mv thm-event thm-name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-constr-to-def-satp-specialized-lemmas ((rels string-setp)
                                                        state)
  :returns (mv (thm-events pseudo-event-form-listp)
               (thm-names symbol-listp))
  :short "Generate local lemmas to apply
          @(tsee constraint-satp-to-definition-satp)
          to specific relations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat analogous to
     @(tsee lift-thm-definition-satp-specialized-lemma) and
     @(tsee lift-thm-constr-satp-specialized-lemma),
     but it is not for the definition @('def') being lifted,
     but instead for the relations called by @('def').
     In the proofs, we need to rewrite @(tsee constraintp)
     to the constraint relations in the body of @('def')
     to equivalent @(tsee definition-satp),
     so that we can apply the lifting theorems for those relations.
     So here we go through all the relations called by @('def')
     and we generate one specialized theorem for each."))
  (b* (((when (set::emptyp rels)) (mv nil nil))
       (rel (set::head rels))
       (pred-name (name-to-symbol rel state))
       (thm-name (acl2::packn-pos
                  (list 'constraint-satp-to-definition-satp-of- pred-name)
                  pred-name))
       (thm-event
        `(defruledl ,thm-name
           (implies (and (primep p)
                         (assignmentp asg)
                         (assignment-wfp asg p)
                         (constraint-case constr :relation)
                         (equal (constraint-relation->name constr)
                                ,rel)
                         (no-duplicatesp-equal
                          (definition->para (lookup-definition ,rel defs))))
                    (b* ((vals (eval-expr-list
                                (constraint-relation->args constr) asg p)))
                      (implies (not (reserrp vals))
                               (equal (constraint-satp constr defs asg p)
                                      (definition-satp
                                        ,rel defs vals p)))))
           :in-theory '(constraint-satp-to-definition-satp)))
       ((mv thm-events thm-names)
        (lift-thm-constr-to-def-satp-specialized-lemmas (set::tail rels)
                                                        state)))
    (mv (cons thm-event thm-events)
        (cons thm-name thm-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm-type-prescriptions-for-called-preds ((rels string-listp)
                                                      state)
  :returns (rules true-listp)
  :short "List of type prescription rules for the shallowly embedded predicates
          for the relations called by the definition being lifted."
  :long
  (xdoc::topstring
   (xdoc::p
    "We need the fact that they are booleans
     in the proofs of the lifting theorems."))
  (b* (((when (endp rels)) nil)
       (rel (car rels))
       (pred-name (name-to-symbol rel state))
       (rule `(:t ,pred-name))
       (rules (lift-thm-type-prescriptions-for-called-preds (cdr rels) state)))
    (cons rule rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-thm ((def definitionp)
                  (def-sat-lemma symbolp)
                  (constr-sat-lemma symbolp)
                  (constr-to-def-sat-lemmas symbol-listp)
                  (prime symbolp)
                  state)
  :returns (mv (event pseudo-event-formp)
               (def-hyps true-listp))
  :short "Generate the theorem connecting
          deeply and shallowly embedded semantics."
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
     The proof is obtained completely by rewriting.
     Note that we use the specialized rules constructed in
     @(tsee lift-thm-definition-satp-specialized-lemma),
     @(tsee lift-thm-constr-satp-specialized-lemma), and
     @(tsee lift-thm-constr-to-def-satp-specialized-lemmas),
     for the reasons discussed in their documentation.
     The proof goes as follows:
     (1) open @(tsee definition-satp) on @('def');
     (2) apply @(tsee constraint-satp-of-relation)
     to the resulting relation constraint for @('def');
     (3) decompose the body of @('def') into the constituent constraints;
     (4) apply @(tsee constraint-satp-to-definition-satp)
     to the relation constraints in the body of @('def');
     (5) apply the lifting theorems for the relations called by @('def'),
     which produces the shallowly embedded predicate calls,
     (6) reduce the equality constraints in @('def')
     to equalities between shallowly embedded expressions, and
     (7) open the shallowly embedded predicate for @('def')
     whose body consists of the shallowly embedded
     equalities and predicate calls.")
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
     we need to leverage the relation between @(tsee omap::assoc)
     and set membership in @(tsee omap::keys),
     given things are formulated;
     perhaps there is a way to do this via rewrite rules."))

  (b* ((wrld (w state))
       ((definition def) def)
       (pred-name (name-to-symbol def.name state))
       (para (name-list-to-symbol-list def.para state))
       (free (definition-free-vars def))
       (quant (name-set-to-symbol-list free state))
       (thm-name (acl2::packn-pos (list 'definition-satp-of-
                                        pred-name
                                        '-to-shallow)
                                  pred-name))
       (def-hyps (lift-thm-def-hyps def wrld))
       (rels (constraint-list-rels def.body))
       (called-lift-thms (lift-thm-called-lift-thms
                          (name-set-to-symbol-list rels state)))
       (type-presc-rules
        (lift-thm-type-prescriptions-for-called-preds rels state))

       ((when (equal free nil))
        (mv
         `(defruled ,thm-name
            (implies (and ,@def-hyps
                          ,@(sesem-gen-fep-terms para prime)
                          (primep ,prime))
                     (equal (definition-satp
                              ,def.name defs (list ,@para) ,prime)
                            (,pred-name ,@para ,prime)))
            :in-theory '(,pred-name
                         (:e ,pred-name)
                         ,def-sat-lemma
                         ,constr-sat-lemma
                         ,@constr-to-def-sat-lemmas
                         ,@called-lift-thms
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
                         (:e set::emptyp)
                         car-cons
                         cdr-cons
                         omap::assoc-of-update
                         acl2::nat-listp-of-cons
                         acl2::not-reserrp-when-nat-listp
                         nfix
                         (:t mod)
                         (:e no-duplicatesp-equal)
                         ,@type-presc-rules))
         def-hyps))

       (constraint-relation-satp-witness
        `(constraint-relation-satp-witness ,def.name
                                           ',(expression-var-list def.para)
                                           defs
                                           (omap::from-lists (list ,@def.para)
                                                             (list ,@para))
                                           ,prime))
       (def-witness `(,(add-suffix-to-fn pred-name "-WITNESS") ,@para ,prime)))

    (mv
     `(defruled ,thm-name
        (implies (and ,@def-hyps
                      ,@(sesem-gen-fep-terms para prime)
                      (primep ,prime))
                 (equal (definition-satp ,def.name defs (list ,@para) ,prime)
                        (,pred-name ,@para ,prime)))
        :in-theory '((:t definition-satp)
                     (:t ,pred-name))
        :use (only-if-direction if-direction)

        :prep-lemmas

        ((defruled only-if-direction
           (implies (and ,@def-hyps
                         ,@(sesem-gen-fep-terms para prime)
                         (primep ,prime))
                    (implies (definition-satp
                               ,def.name defs (list ,@para) ,prime)
                             (,pred-name ,@para ,prime)))
           :in-theory '(,def-sat-lemma
                        ,constr-sat-lemma
                        ,@constr-to-def-sat-lemmas
                        ,@called-lift-thms
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
                        (:e set::emptyp)
                        car-cons
                        cdr-cons
                        omap::assoc-of-update*
                        omap::assoc-of-update
                        acl2::nat-listp-of-cons
                        acl2::not-reserrp-when-nat-listp
                        lift-rule-nfix-when-natp
                        (:t mod)
                        (:t reserr)
                        fty::reserrp-of-reserr
                        lift-rule-omap-consp-of-assoc-iff-assoc
                        (:e set::in)
                        natp-of-cdr-of-in-when-assignmentp-type
                        fep-of-cdr-of-in-when-assignment-wfp
                        (:e no-duplicatesp-equal)
                        ,@type-presc-rules)
           :use ((:instance ,(add-suffix-to-fn pred-name "-SUFF")
                            ,@(lift-thm-free-inst
                               free constraint-relation-satp-witness state))
                 ,@(lift-thm-omap-keys-lemma-instances
                    (append def.para free)
                    constraint-relation-satp-witness)))

         (defruled if-direction
           (implies (and ,@def-hyps
                         ,@(sesem-gen-fep-terms para prime)
                         (primep ,prime))
                    (implies (,pred-name ,@para ,prime)
                             (definition-satp
                               ,def.name defs (list ,@para) ,prime)))
           :in-theory '(,pred-name
                        ,def-sat-lemma
                        ,constr-sat-lemma
                        ,@constr-to-def-sat-lemmas
                        ,@called-lift-thms
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
                        omap::assoc-of-update*
                        omap::assoc-of-update
                        (:e omap::keys)
                        (:e set::insert)
                        len
                        lift-rule-nfix-when-natp
                        (:e reserrp)
                        acl2::not-reserrp-when-natp
                        acl2::not-reserrp-when-nat-listp
                        nat-listp
                        (:e omap::assoc)
                        lift-rule-natp-of-mod
                        (:e natp)
                        (:e no-duplicatesp-equal)
                        acl2::primep-forward-to-posp
                        ,@type-presc-rules
                        pfield::natp-of-add
                        pfield::natp-of-mul)
           :use ((:instance constraint-relation-satp-suff
                            (asgfree (omap::from-lists
                                      (list ,@free)
                                      (list ,@(lift-thm-asgfree-pairs
                                               quant def-witness))))
                            (name ,def.name)
                            (args (expression-var-list (list ,@def.para)))
                            (asg (omap::from-lists (list ,@def.para)
                                                   (list ,@para))))))))
     def-hyps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-table-add ((def definitionp) (hyps true-listp))
  :returns (even pseudo-event-formp)
  :short "Event to update the table of lifted PFCSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This adds an entry to the table for the definition passed as argument."))
  (b* ((info (make-lift-info :def def :hyps hyps)))
    `(table lift-table ,(definition->name def) ',info)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-fn ((def definitionp) (prime symbolp) state)
  :returns (event pseudo-event-formp)
  :short "Lift a deeply embedded PFCS definition
          to a shallowly embedded PFCS definition
          with a theorem relating the two."
  (b* ((event-fn (sesem-definition def prime state))
       ((mv event-def-sat def-sat-lemma)
        (lift-thm-definition-satp-specialized-lemma def state))
       ((mv event-constr-sat constr-sat-lemma)
        (lift-thm-constr-satp-specialized-lemma def state))
       ((mv events-constr-to-def-sat constr-to-def-sat-lemmas)
        (lift-thm-constr-to-def-satp-specialized-lemmas
         (constraint-list-rels (definition->body def)) state))
       ((mv event-thm def-hyps) (lift-thm def
                                          def-sat-lemma
                                          constr-sat-lemma
                                          constr-to-def-sat-lemmas
                                          prime
                                          state))
       (event-table (lift-table-add def def-hyps)))
    `(encapsulate ()
       ,event-fn
       ,event-def-sat
       ,event-constr-sat
       ,@events-constr-to-def-sat
       ,event-thm
       ,event-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+ lift (def &key (prime 'p))
  :short "Macro to lift a deeply embedded PFCS definition
          to a shallowly embedded PFCS definition
          with a theorem relating the two."
  :long
  (xdoc::topstring
   (xdoc::p
    "The required argument must be a ground form
     that evaluates to a PFCS @(tsee definition).
     The form is evaluated and the resulting definition is processed.")
   (xdoc::p
    "The keyword argument must be a symbol
     to use for the prime that parameterizes the PFCS semantics.
     It is @('p') by default.
     This is quoted (not evaluated) for processing."))
  `(make-event (lift-fn ,def ',prime state)))
