; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc definductive

  :parents (std/util)

  :short "Define predicates inductively via inference rules."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Some predicates can be conveniently defined as
      the smallest ones satisfying some given inference rules,
      where an inference rule is an implication of suitable form
      (where `suitable' is elaborated later).")

    (xdoc::p
     "A simple example is that, given a binary relation")
    (xdoc::@[]
     "R \\subseteq \\mathcal{U} \\times \\mathcal{U}")
    (xdoc::p
     "over a universe of values @($\\mathcal{U}$),
      its reflexive and transitive closure can be defined as
      the smallest relation")
    (xdoc::@[]
     "R^\\ast \\subseteq \\mathcal{U} \\times \\mathcal{U}")
    (xdoc::p
     "that satisfies the following inference rules:")
    (xdoc::@[]
     "\\begin{array}{l}
      \\frac {R(x,y)} {R^\\ast(x,y)}\\ \\mathsf{Base}
      \\end{array}
      \\begin{array}{l}
      \\frac {} {R^\\ast(x,x)}\\ \\mathsf{Refl}
      \\end{array}
      \\begin{array}{l}
      \\frac {R^\\ast(x,y) \\quad R^\\ast(y,z)} {R^\\ast(x,z)}\\ \\mathsf{Trans}
      \\end{array}")
    (xdoc::p
     "Rule @($\\mathsf{Base}$) says that
      anything in @($R$) is also in @($R^\\ast$).
      Rule @($\\mathsf{Refl}$) says that @($R^\\ast$) is reflexive.
      Rule @($\\mathsf{Trans}$) says that @($R^\\ast$) is transitive.
      These rules are logical implications,
      but a critical unwritten additional requirement is that
      @($R^\\ast$) be the smallest relation satisfying them.
      For the above rules, @($R^\\ast$) exists and is unique.")

    (xdoc::p
     "Inductive definitions via inference rules are commonly used
      to define logical systems as well as programming language semantics
      (e.g. static typing rules and dynamic execution rules).")

    (xdoc::p
     "In higher-order logic, @($R^\\ast$) can be formalized as follows
      (explained below):")
    (xdoc::@[]
     "\\mathcal{F} :
      \\mathcal{P}(\\mathcal{U}\\times\\mathcal{U})
      \\rightarrow
      \\mathcal{P}(\\mathcal{U}\\times\\mathcal{U})")
    (xdoc::@[]
     "\\mathcal{F}(r) =
      R \\cup
      \\{(x,x) \\mid x \\in \\mathcal{U}\\} \\cup
      \\{(x,z) \\mid \\exists y.\\ r(x,y) \\wedge r(y,z)\\}")
    (xdoc::@[]
     "R^\\ast =
      \\iota r. \\ (
        r = \\mathcal{F}(r) \\wedge
        (\\forall r'.
         \\ r' = \\mathcal{F}(r') \\Longrightarrow r \\subseteq r'))")
    (xdoc::p
     "Here @($\\mathcal{P}$) is the powerset operator.
      The higher-order function @($\\mathcal{F}$)
      maps a generic binary relation @($r$) over @($\\mathcal{U}$)
      to another binary relation @($\\mathcal{F}(r)$) over @($\\mathcal{U}$),
      according to the inference rules:
      if @($R(x,y)$) then @($\\mathcal{F}(r)(x,y)$)
      (rule @($\\mathsf{Base}$));
      unconditionally @($\\mathcal{F}(r)(x,x)$) (rule @($\\mathsf{Refl}$));
      if @($r(x,y)$) and @($r(y,z)$) then @($\\mathcal{F}(r)(x,z)$)
      (rule @($\\mathsf{Trans}$)).
      The function @($\\mathcal{F}$) is easily proved monotone:")
    (xdoc::@[]
     "r_1 \\subseteq r_2 \\Longrightarrow
      \\mathcal{F}(r_1) \\subseteq \\mathcal{F}(r_2)")
    (xdoc::p
     "Thus, by the Knaster-Tarski theorem,
      @($\\mathcal{F}$) has a least fixpoint,
      and we define @($R^\\ast$) to be it,
      via the @($\\iota$) definite description operator:
      @($R^\\ast$) is the relation @($r$) that
      (i) is a fixpoint of @($\\mathcal{F}$) and
      (ii) is no larger than all other fixpoints of @($\\mathcal{F}$).")

    (xdoc::p
     "The above generalizes to multiple predicates,
      defined via mutually recursive inference rules.")

    (xdoc::p
     "Higher-order logic provers typically have mechanisms
      to inductively define predicates
      by writing inference rules in essentially a form like above.
      Under the hood, the prover turns that into
      the higher-order definition,
      at the same time checking that the rules are monotone
      (i.e. that the @($\\mathcal{F}$) derived from the rules is monotone).")

    (xdoc::p
     "Since ACL2 is first-order, we cannot quite do the same.
      But we can achieve the same effect
      by reifying proof trees built using the inference rules
      and by defining the predicates of interest
      in terms of the existence of such proof trees.
      This macro does that:
      given signatures for one or more predicates to define inductively,
      and given the inference rules that define them inductively,
      the macro generates the proof tree data structures,
      the notion of valid proof trees according to the rules,
      the definitions of the predicates,
      implication theorems that correspond to the inference rules,
      and theorems showing that the defined predicates are
      the smallest ones that satisfy the inference rules.
      In order to generate these artifacts,
      the macro performs sufficient checks for the monotonicity of the rules."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(definductive name"
     "              :preds   ...  ; required, no default"
     "              :irules  ...  ; required, no default"
     "              :parents ...  ; no default"
     "              :short   ...  ; no default"
     "              :long    ...  ; no default"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "Name for this inductive definition instance.")
     (xdoc::p
      "It must be a symbol.")
     (xdoc::p
      "It is used as name of the generated XDOC topic (if any, see below).
       In the future, it may be used to identify this inductive definition.")
     (xdoc::p
      "The names of all the generated events,
       except possibly for the predicates, whose names are supplied directly,
       are in the package of this symbol.
       It is recommended to put this name and the predicate names
       all in the same package."))

    (xdoc::desc
     "@(':preds') &mdash; required, no default"
     (xdoc::p
      "Predicates to define inductively.")
     (xdoc::p
      "It must be a list of the form")
     (xdoc::codeblock
      "((p[1] x[1,1] ... x[1,m[1]])"
      " ..."
      " (p[n] x[n,1] ... x[n,m[n]]))")
     (xdoc::p
      "where each @('p[i]') is a symbol that names a predicate,
       and each @('x[i,j]') is a symbol that names a formal of @('p[i]').
       Each @('p[i]') has @('m[i]') formals,
       where @('m[i]') must be positive.")
     (xdoc::p
      "There must be at least one predicate, i.e. @('n') must be positive.")
     (xdoc::p
      "The symbols @('p[1]'), ..., @('p[n]') must be all distinct.")
     (xdoc::p
      "For each @('i'),
       the symbols @('x[i,1]'), ..., @('x[i,m[i]]') must be all distinct.")
     (xdoc::p
      "Currently, this macro only supports one predicate,
       i.e. @('n') must be 1.
       We plan to extend the macro soon.")
     (xdoc::p
      "We also plan to add support for guards to the predicates,
       and likely the ability for @('x[i,j]') to be "
      (xdoc::seetopic "std::extended-formals" "extended formals")
      " as in @(tsee define)."))

    (xdoc::desc
     "@(':irules') &mdash; required, no default"
     (xdoc::p
      "Inference rules that define the predicates.")
     (xdoc::p
      "It must be a list of the form")
     (xdoc::codeblock
      "((rule[1] (premise[1,1] ... premise[1,q[1]]) conclusion[1])"
      " ..."
      " (rule[r] (premise[r,1] ... premise[r,q[r]]) conclusion[r]))")
     (xdoc::p
      "where each @('rule[k]') is a symbol that names a rule,
       and each @('premise[k,h]') and @('conclusion[k]') is
       either (i) a term @('(p[i] arg[1] ... arg[m[i]])')
       where none of @('p[1]'), ..., @('p[n]') occurs in
       any of @('arg[1]'), ..., @('arg[m[i]]'),
       or (ii) a term in which none of @('p[1]'), ..., @('p[n]') occurs.
       For a @('conclusion[k]'), the term must have form (i);
       for a @('premise[k,h]'), the term may have either form.
       All the rule names @('rule[1]'), ..., @('rule[r]') must be distinct;
       there must be at least one rule, i.e. @('r') must be positive.")
     (xdoc::p
      "The predicates being defined must be all mutually recursive:
       every predicate must depend on itself and on every other predicate,
       directly or indirectly,
       where a predicate @('p[i]') depends on a predicate @('p[j]') when
       some rule has @('p[i]') in its conclusion and @('p[j]') in some premise.
       For a single predicate (the only case currently supported),
       this means that there must be at least one rule
       with a premise of the form (i) above;
       without such a recursive rule,
       the predicate could be more simply defined
       without using inference rules.
       Predicates that are not all mutually recursive
       should be defined by separate uses of this macro,
       in dependency order.")
     (xdoc::p
      "There must be at least one rule
       whose premises all have the form (ii) above.
       That is, there must be at least one base case
       for the recursive definition,
       otherwise the smallest predicate satisfying the rules is empty.
       This condition will be generalized when
       we remove the restriction to one predicate mentioned above."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are put into the generated XDOC topic
       described in the Section `Generated Events' below.
       If @(':parents') is supplied, it must not be @('nil').")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('name')"
     (xdoc::p
      "An XDOC topic whose name is given by the @('name') input.
       This is generated iff
       at least one of the @(':parents'), @(':short'), and @(':long') inputs
       is provided,
       in which case they populate the XDOC topic.")
     (xdoc::p
      "If generated,
       this XDOC topic is generated with @(tsee defxdoc+),
       with @(':order-topics t'),
       so that the other generated events (described below),
       which all have this XDOC topic as parent,
       are listed in order as subtopics.")
     (xdoc::p
      "If this XDOC topic is generated,
       the functions and theorems below are accompanied by XDOC,
       and they all have this XDOC topic as parent."))

    (xdoc::desc
     (list
      "@('p[1]-assertion')"
      "@('...')"
      "@('p[n]-assertion')")
     (xdoc::p
      "@(tsee fty::defprod) fixtypes that reify the predicates' assertions.
       The fixtype for @('p[i]') consists of
       fields corresponding to @('x[i,1]'), ..., @('x[i,m[i]]')."))

    (xdoc::desc
     (list
      "@('p[1]-proof')"
      "@('...')"
      "@('p[n]-proof')")
     (xdoc::p
      "@(tsee fty::deftagsum) fixtypes that reify
       (the structure of) proof trees corresponding to the rules.
       Each fixtype has a summand
       for each rule whose conclusion is @('(p[i] ...)'):
       the summand has a field of type @('p[i]-assertion') for the conclusion,
       as well as zero or more fields
       for each premise of the form @('(p[j] ...)'),
       whose corresponding field has type @('p[j]-proof').")
     (xdoc::p
      "These fixtypes are mutually recursive in general,
       in which case they are put inside a @(tsee fty::deftypes);
       currently, since only one predicate is supported,
       a single @(tsee fty::deftagsum) is generated."))

    (xdoc::desc
     (list
      "@('p[1]-proof->conclusion')"
      "@('...')"
      "@('p[n]-proof->conclusion')")
     (xdoc::p
      "Function to return the conclusion, of type @('p[i]-assertion'),
       of each value of the @('p[i]-proof') fixtype.
       As described above, each summand has a conclusion field.")
     (xdoc::p
      "This function is guard-verified and has fixing theorems."))

    (xdoc::desc
     (list
      "@('p[l[1]]-rule[1]-validp')"
      "@('...')"
      "@('p[l[r]]-rule[r]-validp')")
     (xdoc::p
      "Predicates saying which combinations of conclusion and premise assertions
       are valid instances of the inference rules.
       For each rule @('rule[k]'),
       whose conclusion is @('p[l[k]]')
       (i.e. @('l[k]') yields the index of
       the predicate used in the conclusion of rule @('k')),
       @('p[l[k]]-rule[k]-validp') takes as inputs
       a conclusion of type @('p[l[k]]-assertion')
       and zero or more premises of the appropriate assertion types,
       and says whether they fit the pattern of the rule,
       i.e. they form a valid instance of the rule.")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they may involve arbitrary user-supplied terms.
       These predicates have fixing theorems."))

    (xdoc::desc
     (list
      "@('p[1]-proof-validp')"
      "@('...')"
      "@('p[n]-proof-validp')")
     (xdoc::p
      "Predicates expressing the validity of proof trees:
       every node of the tree must be
       a valid instance of the corresponding inference rule,
       according to the @('p[l[k]]-rule[k]-validp') predicates.")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[l[k]]-rule[k]-validp') predicates.
       The @('p[i]-proof-validp') predicates have fixing theorems."))

    (xdoc::desc
     (list
      "@('p[1]')"
      "@('...')"
      "@('p[n]')")
     (xdoc::p
      "Definitions of the predicates,
       in terms of the existence of valid proof trees.")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[i]-proof-validp') predicates.
       The @('p[i]') predicates do not have fixing theorems,
       because the formals are currently untyped."))

    (xdoc::desc
     (list
      "@('p[l[1]]-proof-for-rule[1]')"
      "@('...')"
      "@('p[l[r]]-proof-for-rule[r]')")
     (xdoc::p
      "Functions to construct
       proof trees of conclusions
       from proofs of premises,
       for all the inference rules.
       These functions are accompanied by theorems showing that
       the output proof trees are valid if the input proof trees are valid.")
     (xdoc::p
      "These functions are used to prove the theorems described next.")
     (xdoc::p
      "Currently these functions
       are not guard-verified,
       because they may involve arbitrary user-supplied terms,
       and do not have fixing theorems,
       because they are only used to prove some of the generated theorems."))

    (xdoc::desc
     (list
      "@('p[l[1]]-rule[1]')"
      "@('...')"
      "@('p[l[r]]-rule[r]')")
     (xdoc::p
      "Theorems showing that the predicates satisfy the rule.
       The theorem for each rule is an implication
       whose antecedents are the premises
       and whose consequent is the conclusion.
       Both premises of forms (i) and (ii) (see above) are included.
       For a rule without premises,
       the theorem is just the conclusion, without implication.")
     (xdoc::p
      "If XDOC is generated, all these theorems are put
       in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix @('-rules')."))

    (xdoc::p
     "The following items serve as validation,
      to show that the predicates defined via the preceding events
      are indeed the smallest ones.
      The generation of the following items
      could be perhaps made optional in this macro.
      If XDOC is generated, all the following items are put
      inside a @(tsee defsection) whose name is obtained by
      extending the @('name') input with the suffix @('-minimal').")

    (xdoc::desc
     (list
      "@('p[1]-alt')"
      "@('...')"
      "@('p[n]-alt')")
     (xdoc::p
      "Uninterpreted functions, introduced via @(tsee defstub),
       used as generic placeholders for alternate predicates
       that also satisfy all the inference rules,
       and that are shown to be no smaller than @('p[1]'), ..., @('p[n]')."))

    (xdoc::desc
     (list
      "@('p[l[1]]-alt-rule[1]-p')"
      "@('...')"
      "@('p[l[r]]-alt-rule[r]-p')")
     (xdoc::p
      "Nullary @(tsee defun-sk) functions saying that
       the uninterpreted @('alt') predicates
       satisfy the rules.
       The bodies of these functions are implications
       with the premises as antecedents
       and with the conclusions as consequents,
       quantified over the free variables in the rules.
       For a rule without premises,
       the body is just the conclusion, without implication.
       For a rule without free variables,
       there is no quantification,
       and a nullary @(tsee defun) is generated instead.")
     (xdoc::p
      "These functions are currently not guard-verified,
       because they may involve arbitrary user-supplied terms.
       These functions have no fixing theorems, because they have no formals."))

    (xdoc::desc
     (list
      "@('p[1]-alt-when-proof-validp')"
      "@('...')"
      "@('p[n]-alt-when-proof-validp')")
     (xdoc::p
      "Theorems saying that,
       if the @(tsee defun-sk)s just above hold,
       then the validity of each proof tree
       with conclusion @('(p[i] x[i,1] ... x[i,m[i]])')
       implies that @('(p[i]-alt x[i,1] ... x[i,m[i]])') holds.
       That is, a proof for @('p[i]') is also a proof for @('p[i]-alt')."))

    (xdoc::desc
     (list
      "@('p[1]-alt-when-p[1]')"
      "@('...')"
      "@('p[n]-alt-when-p[n]')")
     (xdoc::p
      "Theorems saying that,
       if the @(tsee defun-sk)s just above hold,
       then the alternate predicates hold whenever the defined ones do.
       That is, the defined predicates are the smallest ones
       among those that satisfy the inference rules.")))))
