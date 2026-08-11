; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

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
      For the above rules, @($R^\\ast$) exists.")

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
      the macro performs sufficient checks for the monotonicity of the rules.")

    (xdoc::p
     "This macro currently generates two representations of proofs,
      and thus two versions of each predicate.
      In the first, each node of a proof carries
      the variables of the rule that builds it,
      and the arguments of the conclusion are arguments
      of the proof validity predicate.
      In the second, each node carries instead its own conclusion
      and the validity of a proof is a predicate of the proof alone.
      The two versions have the same interface:
      the same introduction rule theorems and the same minimality theorems.
      Each is therefore a least relation satisfying the rules,
      and so the two are the same;
      this macro proves that, as described below.
      We generate both representations while we compare them;
      eventually we may keep just one."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(definductive name"
     "              :preds   ...  ; required, no default"
     "              :irules  ...  ; required, no default"
     "              :parents ...  ; no default"
     "              :short   ...  ; no default"
     "              :long    ...  ; no default"
     "              :print   ...  ; default :result"
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
      "In the future we may add support for guards to the predicates,
       and the ability for @('x[i,j]') to be "
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
       The names of the rules with the same predicate in the conclusion
       must be distinct;
       rules with different predicates in the conclusions
       may have the same name.
       There must be at least one rule, i.e. @('r') must be positive.")
     (xdoc::p
      "Each predicate @('p[i]') must be
       in the conclusion of at least one rule.")
     (xdoc::p
      "A predicate @('p[i]') depends on a predicate @('p[j]') when
       some rule has @('p[i]') in its conclusion and @('p[j]') in some premise,
       or, transitively, when @('p[i]') depends on a predicate
       that depends on @('p[j]').
       A predicate is singly recursive when it depends on itself.
       Two or more predicates are mutually recursive when
       they all depend on each other.")
     (xdoc::p
      "The predicates are partitioned into cliques of mutual dependency:
       two different predicates are in the same clique
       when each one depends on the other.
       Thus each clique consists of
       either two or more mutually recursive predicates,
       or a single predicate, which may or may not be singly recursive.
       The cliques are ordered by dependency,
       which is always possible because
       the dependencies between different cliques form no cycles;
       the events generated for each clique come after
       the ones generated for the cliques it depends on.")
     (xdoc::p
      "The predicates of each clique are organized into levels, as follows.
       A predicate is at level 0 if some rule has it in its conclusion
       and no premises of the form (i) above
       that call predicates of the same clique;
       premises that call predicates of preceding cliques are allowed,
       since those predicates are already defined.
       A predicate is at level @('L+1') if some rule has it in its conclusion
       and all its premises of the form (i)
       that call predicates of the same clique
       call predicates at level @('L') or lower.
       Every predicate must be at some level.
       For a predicate that forms a singleton clique,
       being at some level amounts to being at level 0,
       i.e. to the existence of a rule with no premises
       that call the predicate itself.")
     (xdoc::p
      "The variables of a rule must differ from
       the variables that the events for the first representation of proofs
       use for the arguments of the conclusion,
       which are @('concl.x[i,1]'), ..., @('concl.x[i,m[i]]'),
       differ from the names of the fields
       that hold the proofs of the premises,
       which are @('premise[1]-proof'), @('premise[2]-proof'), and so on,
       and differ from @('proof$'),
       which is the variable of the fixtypes of proofs
       of that representation."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are put into the generated XDOC topic
       described in the Section `Generated Events' below.
       If @(':parents') is supplied, it must not be @('nil')."))

    (xdoc::desc
     "@(':print') &mdash; default @(':result')"
     (xdoc::p
      "Specifies what is printed on the screen.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':error'), to print only error output (if any).")
      (xdoc::li
       "@(':result'), to print, besides any error output,
        also the "
       (xdoc::seetopic "event-macro-results" "results")
       " of @('definductive').
        This is the default value of the @(':print') input.
        Since the results may consist of a relatively large number of events,
        only their names are printed;
        the event themselves can be inspected via
        ACL2's facilities, e.g. "
       (xdoc::seetopic "pe" "@(':pe')")
       ".")
      (xdoc::li
       "@(':info'), to print,
        besides any error output and the results,
        also some additional information about
        the internal operation of @('definductive').
        (Currently there is no difference between
        the @(':info') and the @(':result') outputs,
        but we plan to add @(':info') outputs.).")
      (xdoc::li
       "@(':all'), to print,
        besides any error output,
        the results,
        and the additional information,
        also ACL2's output in response to all the submitted events.
        This could be a lot of output."))
     (xdoc::p
      "The errors are printed as "
      (xdoc::seetopic "set-inhibit-output-lst" "error output")
      ". The results and the additional information are printed as "
      (xdoc::seetopic "set-inhibit-output-lst" "comment output")
      ". The ACL2 output enabled by @(':print :all') may consist of "
      (xdoc::seetopic "set-inhibit-output-lst" "output of various kinds")
      ".")
     (xdoc::p
      "If @(':print') is @(':error') or @(':result') or @(':info'),
       @('definductive') suppresses
       all kinds of outputs (via @(tsee with-output))
       except for error and comment output
       (the latter is used for the @(':result') and @(':info') output).
       Otherwise, @('definductive') does not suppress any output.
       However, the actual output depends on
       which outputs are enabled or not prior to the call of @('definductive'),
       including any @(tsee with-output) with which
       the user may wrap the call of @('definductive').")))

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
      "@('p[1]-proof')"
      "@('...')"
      "@('p[n]-proof')")
     (xdoc::p
      "@(tsee fty::deftagsum) fixtypes that reify
       (the structure of) proof trees corresponding to the rules.
       Each fixtype has a summand
       for each rule whose conclusion is @('(p[i] ...)'):
       the summand has a field for each free variable of the rule,
       named after the variable and having no type,
       as well as zero or more fields
       for each premise of the form @('(p[j] ...)'),
       whose corresponding field has type @('p[j]-proof').")
     (xdoc::p
      "One event is generated for each clique of predicates
       (see the @(':irules') input), in dependency order.
       For a clique of a single predicate,
       the event is a @(tsee fty::deftagsum).
       For a clique of two or more predicates,
       the fixtypes are mutually recursive,
       and the event is a @(tsee fty::deftypes)
       named after the first predicate of the clique,
       with the suffix @('-proof-clique')."))

    (xdoc::desc
     (list
      "@('p[l[1]]-rule[1]-validp')"
      "@('...')"
      "@('p[l[r]]-rule[r]-validp')")
     (xdoc::p
      "Predicates saying whether the conditions of each rule hold,
       except for the ones about the proofs of the premises.
       For each rule @('rule[k]'),
       whose conclusion is @('p[l[k]]')
       (i.e. @('l[k]') yields the index of
       the predicate used in the conclusion of rule @('k')),
       @('p[l[k]]-rule[k]-validp') takes as inputs
       the arguments of the conclusion
       and the free variables of the rule,
       and says whether the premises that are not
       calls of the predicates being defined hold,
       and whether the arguments of the conclusion
       are the ones that the rule derives.")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they may involve arbitrary user-supplied terms."))

    (xdoc::desc
     (list
      "@('p[1]-proof-validp')"
      "@('...')"
      "@('p[n]-proof-validp')")
     (xdoc::p
      "Predicates expressing the validity of proof trees:
       every node of the tree must be
       a valid instance of the corresponding inference rule,
       according to the @('p[l[k]]-rule[k]-validp') predicates.
       Each takes the arguments of the conclusion as arguments,
       recurs on the proofs of the premises,
       and calls @('p[l[k]]-rule[k]-validp') for the rest.")
     (xdoc::p
      "As with the fixtypes of proofs,
       one event is generated for each clique of predicates,
       in dependency order.
       For a clique of a single predicate,
       the event is a @(tsee define).
       For a clique of two or more predicates,
       the functions are mutually recursive,
       and the event is a @(tsee defines)
       named after the first predicate of the clique,
       with the suffix @('-proof-validp-clique').")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they may involve arbitrary user-supplied terms.
       The @('p[i]-proof-validp') predicates have fixing theorems."))

    (xdoc::desc
     (list
      "@('p[1]')"
      "@('...')"
      "@('p[n]')")
     (xdoc::p
      "Definitions of the predicates,
       in terms of the existence of valid proof trees:
       @('(p[i] x[i,1] ... x[i,m[i]])') holds when
       there is a proof that is valid for those arguments,
       which are passed to @('p[i]-proof-validp').")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[i]-proof-validp') predicates.
       The @('p[i]') predicates do not have fixing theorems,
       because the formals are currently untyped."))

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
      "Constrained functions, introduced via an @(tsee encapsulate),
       used as generic placeholders for alternate predicates
       that also satisfy all the inference rules,
       and that are shown to be no smaller than @('p[1]'), ..., @('p[n]').
       The constraints are the theorems described next.
       The witnesses are @('p[1]'), ..., @('p[n]') themselves,
       which satisfy the constraints by the rule theorems."))

    (xdoc::desc
     (list
      "@('p[l[1]]-alt-rule[1]')"
      "@('...')"
      "@('p[l[r]]-alt-rule[r]')")
     (xdoc::p
      "Theorems, exported by the aforementioned @(tsee encapsulate),
       constraining the @('p[i]-alt') functions to satisfy the rules.
       Each is an implication
       with the premises as antecedents
       and with the conclusion as consequent,
       with the @('p[i]-alt') functions in place of the predicates.
       For a rule without premises,
       the theorem is just the conclusion, without implication.
       These theorems are disabled, like the rule theorems."))

    (xdoc::desc
     (list
      "@('p[1]-alt-when-proof-validp')"
      "@('...')"
      "@('p[n]-alt-when-proof-validp')")
     (xdoc::p
      "Theorems saying that the validity of each proof tree
       for conclusion arguments @('x[i,1]'), ..., @('x[i,m[i]]')
       implies that @('(p[i]-alt x[i,1] ... x[i,m[i]])') holds.
       That is, a proof for @('p[i]') is also a proof for @('p[i]-alt').")
     (xdoc::p
      "As with the fixtypes of proofs and the proof validity predicates,
       these theorems are generated one clique at a time,
       in dependency order:
       the ones of a clique of two or more predicates are proved together,
       by mutual induction on the @('p[i]-proof-validp') predicates,
       while the theorems of the preceding cliques
       play, for the premises that call predicates of those cliques,
       the role that the induction hypothesis plays
       for the premises that call predicates of the same clique."))

    (xdoc::desc
     (list
      "@('p[1]-alt-when-p[1]')"
      "@('...')"
      "@('p[n]-alt-when-p[n]')")
     (xdoc::p
      "Theorems saying that the alternate predicates hold
       whenever the defined ones do.
       That is, the defined predicates are the smallest ones
       among those that satisfy the inference rules."))

    (xdoc::p
     "The following items are the second representation of proofs,
      described in the Section `Introduction' above.
      Neither representation is used to define or prove the other;
      the theorems described last relate the two.")

    (xdoc::desc
     (list
      "@('p[1]-2-assertion')"
      "@('...')"
      "@('p[n]-2-assertion')")
     (xdoc::p
      "@(tsee fty::defprod) fixtypes that reify the predicates' assertions.
       The fixtype for @('p[i]-2') consists of
       fields corresponding to @('x[i,1]'), ..., @('x[i,m[i]]').
       There is no counterpart of these fixtypes
       in the other representation of proofs,
       where the conclusion is not part of a proof."))

    (xdoc::desc
     (list
      "@('p[1]-2-proof')"
      "@('...')"
      "@('p[n]-2-proof')")
     (xdoc::p
      "@(tsee fty::deftagsum) fixtypes that reify proofs,
       as @('p[i]-proof') does, but under a different representation.
       Each summand has a field of type @('p[i]-2-assertion')
       for the conclusion,
       and the same fields for the proofs of the premises,
       of the @('p[j]-2-proof') types,
       but no fields for the variables of the rule.")
     (xdoc::p
      "As with the @('p[i]-proof') fixtypes,
       one event is generated for each clique of predicates,
       in dependency order,
       a @(tsee fty::deftagsum) or a @(tsee fty::deftypes)
       named after the first predicate of the clique,
       with the suffix @('-proof-clique')."))

    (xdoc::desc
     (list
      "@('p[1]-2-proof->conclusion')"
      "@('...')"
      "@('p[n]-2-proof->conclusion')")
     (xdoc::p
      "Function to return the conclusion, of type @('p[i]-2-assertion'),
       of each value of the @('p[i]-2-proof') fixtype.
       As described above, each summand has a conclusion field.")
     (xdoc::p
      "This function is guard-verified and has fixing theorems."))

    (xdoc::desc
     (list
      "@('p[l[1]]-2-rule[1]-validp')"
      "@('...')"
      "@('p[l[r]]-2-rule[r]-validp')")
     (xdoc::p
      "Predicates saying which combinations of
       conclusion and premise assertions
       are valid instances of the inference rules.
       Each @('p[l[k]]-2-rule[k]-validp') takes as inputs
       a conclusion of type @('p[l[k]]-2-assertion')
       and zero or more premises of the appropriate assertion types,
       and says whether they fit the pattern of the rule,
       i.e. they form a valid instance of the rule.
       Unlike @('p[l[k]]-rule[k]-validp'),
       each is a @(tsee std::define-sk)
       that quantifies over the variables of the rule,
       except that it is an ordinary @(tsee define)
       for a rule without variables.")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they may involve arbitrary user-supplied terms.
       These predicates have fixing theorems."))

    (xdoc::desc
     (list
      "@('p[1]-2-proof-validp')"
      "@('...')"
      "@('p[n]-2-proof-validp')")
     (xdoc::p
      "Predicates expressing the validity of proof trees,
       as @('p[i]-proof-validp') does,
       but as predicates of the proof alone:
       the conclusion is a field of the proof
       rather than arguments of the predicate.
       As with the fixtypes of proofs,
       one event is generated for each clique of predicates,
       a @(tsee define) or a @(tsee defines)
       named after the first predicate of the clique,
       with the suffix @('-proof-validp-clique').")
     (xdoc::p
      "In general these predicates cannot be executed,
       because the @('p[l[k]]-2-rule[k]-validp') predicates that they call
       are @(tsee std::define-sk)s, unless every rule is ground.
       These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[l[k]]-2-rule[k]-validp') predicates.
       The @('p[i]-2-proof-validp') predicates have fixing theorems."))

    (xdoc::desc
     (list
      "@('p[1]-2')"
      "@('...')"
      "@('p[n]-2')")
     (xdoc::p
      "Definitions of the predicates,
       in terms of the existence of valid proofs,
       as for @('p[i]'), but with the conclusion of the proof
       compared with the assertion built from the arguments,
       instead of the arguments being passed
       to the proof validity predicate."))

    (xdoc::desc
     (list
      "@('p[l[1]]-2-proof-for-rule[1]')"
      "@('...')"
      "@('p[l[r]]-2-proof-for-rule[r]')")
     (xdoc::p
      "Functions to construct
       proof trees of conclusions
       from proofs of premises,
       for all the inference rules.
       These functions are accompanied by theorems showing that
       the output proof trees are valid if the input proof trees are valid.")
     (xdoc::p
      "These functions are used to prove
       the @('p[l[k]]-2-rule[k]') theorems described next;
       the proofs of the @('p[l[k]]-rule[k]') theorems
       use the proof constructors directly instead,
       so there is no counterpart of these functions
       in the other representation of proofs.")
     (xdoc::p
      "Currently these functions
       are not guard-verified,
       because they may involve arbitrary user-supplied terms,
       and do not have fixing theorems,
       because they are only used to prove some of the generated theorems."))

    (xdoc::desc
     (list
      "@('p[l[1]]-2-rule[1]')"
      "@('...')"
      "@('p[l[r]]-2-rule[r]')")
     (xdoc::p
      "Theorems showing that the @('p[i]-2') predicates satisfy the rules.
       These have the same statements as
       @('p[l[k]]-rule[k]'),
       with @('p[i]-2') in place of @('p[i]').")
     (xdoc::p
      "If XDOC is generated, all these theorems are put
       in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix @('-2-rules')."))

    (xdoc::desc
     (list
      "@('p[i]-2-alt')"
      "@('p[l[k]]-2-alt-rule[k]')"
      "@('p[i]-2-alt-when-proof-validp')"
      "@('p[i]-2-alt-when-p[i]-2')")
     (xdoc::p
      "The counterparts, for the @('p[i]-2') predicates,
       of the items for minimality described above.
       They have the same form,
       and the same statements with @('p[i]-2') in place of @('p[i]'),
       except for the @('p[i]-2-alt-when-proof-validp') theorems:
       there the conclusion is a field of the proof,
       which the theorem destructures,
       instead of arguments of the proof validity predicate.")
     (xdoc::p
      "If XDOC is generated, all these items are put
       in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix @('-2-minimal')."))

    (xdoc::desc
     (list
      "@('p[i]-2-when-p[i]')"
      "@('p[i]-when-p[i]-2')"
      "@('p[i]-2-is-p[i]')")
     (xdoc::p
      "Theorems saying that the two representations of proofs
       define the same predicates.
       Each inclusion follows from the minimality theorem of one of the two,
       used with the predicate of the other
       in place of the constrained function:
       what remains to prove is that the latter satisfies the rules,
       which its rule theorems say.
       The equality follows from the two inclusions,
       since both predicates are booleans.")
     (xdoc::p
      "If XDOC is generated, all these theorems are put
       in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix @('-2-same').")))))
