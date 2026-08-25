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
      "It is used as name of the generated XDOC topic (if any, see below),
       and as prefix of the name of the generated ruleset (see below).
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
       the variables that the events for the representation of proofs
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
       because they may involve arbitrary user-supplied terms.")
     (xdoc::p
      "These predicates are disabled;
       they are added to the ruleset described below."))

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
       The @('p[i]-proof-validp') predicates have fixing theorems.")
     (xdoc::p
      "These predicates are disabled;
       they are added to the ruleset described below."))

    (xdoc::desc
     "@('name-validp-defs')"
     (xdoc::p
      "A "
      (xdoc::seetopic "rulesets" "ruleset")
      ", whose name is obtained by
       extending the @('name') input with the suffix @('-validp-defs'),
       with the definitions of
       the @('p[l[k]]-rule[k]-validp') and @('p[i]-proof-validp') predicates.")
     (xdoc::p
      "Since those predicates are disabled,
       this ruleset provides a way to enable all of them at once,
       e.g. via @(tsee enable*),
       when reasoning about proof trees."))

    (xdoc::desc
     (list
      "@('p[1]-proof-minimalp')"
      "@('...')"
      "@('p[n]-proof-minimalp')")
     (xdoc::p
      "Predicates saying that a proof tree is minimal,
       i.e. that no valid proof tree of the same conclusion
       has a smaller count.
       Each takes a proof and the arguments of the conclusion,
       and universally quantifies over the other proof trees.")
     (xdoc::p
      "Each predicate is defined by a @(tsee std::define-sk).")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[i]-proof-validp') predicates.")
     (xdoc::p
      "These predicates are disabled,
       and so are their associated @('-necc') theorems."))

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
      "Each predicate is defined by a @(tsee std::define-sk).
       The witness function backing the existential
       is given the name @('p[i]-proof').")
     (xdoc::p
      "The proof whose existence is asserted is also required to be minimal,
       according to @('p[i]-proof-minimalp').
       This does not change the meaning of the predicates,
       because a minimal valid proof tree exists
       exactly when any valid proof tree exists.
       It makes the witness @('p[i]-proof') a minimal proof,
       which supports reasoning by induction
       using the @('p[i]-induct') functions (see below).
       (A minimal proof tree need not be unique:
       there may be several valid proof trees for the same conclusion
       with the same count.)")
     (xdoc::p
      "These predicates are currently not guard-verified,
       because they call the non-guard-verified
       @('p[i]-proof-validp') predicates.
       The @('p[i]') predicates do not have fixing theorems,
       because the formals are currently untyped.")
     (xdoc::p
      "These predicates are disabled,
       and so are their associated @('-suff') theorems."))

    (xdoc::desc
     (list
      "@('p[1]-when-proof-validp')"
      "@('...')"
      "@('p[n]-when-proof-validp')")
     (xdoc::p
      "Theorems saying that @('(p[i] x[i,1] ... x[i,m[i]])') holds
       if there is any valid proof tree for those arguments,
       whether or not that proof tree is minimal.")
     (xdoc::p
      "Because of the minimality requirement described above,
       the @('p[i]-suff') theorems that @(tsee defun-sk) generates
       require the proof tree to be minimal.
       These theorems drop that requirement.")
     (xdoc::p
      "The validity hypothesis precedes the recognizer hypothesis,
       so that, when the theorem is used as a rewrite rule,
       free variable matching binds the proof tree from the former
       rather than from the weaker latter.")
     (xdoc::p
      "If XDOC is generated,
       these theorems and the @('p[i]-proof-count-bound') theorems below
       are put in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix @('-valid-proofs').")
     (xdoc::p
      "These theorems are enabled."))

    (xdoc::desc
     (list
      "@('p[1]-proof-count-bound')"
      "@('...')"
      "@('p[n]-proof-count-bound')")
     (xdoc::p
      "Theorems saying that the witness proof tree produced by @('p[i]-proof')
       is minimal in fact,
       i.e. that its count is no larger than the count of
       any valid proof tree of the same conclusion.
       These are @(':linear') rules,
       triggered on the count of the witness.")
     (xdoc::p
      "This is what ties the proof tree obtained from the existential
       back to a concrete proof tree,
       which the measure of the induction schemes below needs.
       As with the minimality predicates,
       the validity hypothesis comes first,
       so that free variable matching binds the proof tree from it;
       that is what lets these theorems apply on their own
       in those measure proofs.")
     (xdoc::p
      "These are generated only for the recursive predicates.
       If XDOC is generated, they go in the @(tsee defsection)
       mentioned just above.")
     (xdoc::p
      "These theorems are disabled."))

    (xdoc::desc
     (list
      "@('p[1]-induct')"
      "@('...')"
      "@('p[n]-induct')")
     (xdoc::p
      "Functions providing an induction scheme for the predicates.
       Each recurses on the arguments of the premises
       of the rule that the witness proof tree used.
       The witness proof is chosen at each step,
       and therefore is not an argument to the function;
       that is what lets it serve as an induction scheme
       for the predicate itself.
       The results of these functions are irrelevant:
       only their recursive structure matters.")
     (xdoc::p
      "One event is generated for each clique of predicates.
       For a clique of a single predicate, the event is a @(tsee define).
       For a clique of two or more predicates,
       the functions are mutually recursive,
       and the event is a @(tsee defines)
       named after the first predicate of the clique,
       with the suffix @('-induct-clique');
       it is generated with @(':flag-local nil'),
       so that the flag macro it generates
       can be used after the call of this macro,
       and with explicit names for that macro and its flag function,
       described just below.")
     (xdoc::p
      "These are generated only for the recursive predicates:
       a non-recursive predicate admits no induction scheme.")
     (xdoc::p
      "These functions are disabled."))

    (xdoc::desc
     (list
      "@('p[1]-induction')"
      "@('...')"
      "@('p[n]-induction')")
     (xdoc::p
      "Rules that make @('p[i]-induct') the induction scheme suggested by
       a call of @('p[i]'), so that a plain @(':induct') hint on such a call
       performs rule induction.")
     (xdoc::p
      "These are generated only for a clique of a single predicate.
       ACL2 derives no induction scheme from mutually recursive functions,
       and so rejects such a rule for a clique of two or more predicates.
       Nor would such a rule suffice there:
       the induction hypothesis for a premise that calls
       a different predicate of the clique
       would be about the predicate being defined instead.
       Mutual rule induction needs the whole clique proved together,
       so the interface for such a clique is instead
       the flag macro generated by the @(tsee defines) described above,
       which is named @('defthm-p[i]-induction'),
       after the first predicate of the clique;
       its flag function is named @('p[i]-induct-flag').")
     (xdoc::p
      "If XDOC is generated, these rules are put
       in a @(tsee defsection) whose name is obtained by
       extending the @('name') input with the suffix
       @('-induction-rules'):
       the suffix is not just @('-induction'),
       because that is the name of one of these very rules
       when a predicate is named as the @('name') input.")
     (xdoc::p
      "These theorems are enabled."))

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
       extending the @('name') input with the suffix @('-rules').")
     (xdoc::p
      "These theorems are disabled."))

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
       the theorem is just the conclusion, without implication.")
     (xdoc::p
      "These theorems are disabled."))

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
       for the premises that call predicates of the same clique.")
     (xdoc::p
      "These theorems are disabled."))

    (xdoc::desc
     (list
      "@('p[1]-alt-when-p[1]')"
      "@('...')"
      "@('p[n]-alt-when-p[n]')")
     (xdoc::p
      "Theorems saying that the alternate predicates hold
       whenever the defined ones do.
       That is, the defined predicates are the smallest ones
       among those that satisfy the inference rules.")
     (xdoc::p
      "These theorems are disabled.")))))
