; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc deftreeops

  :parents (abnf)

  :short "Generate grammar-specific operations on trees."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "The ABNF @(see semantics) includes tree matching predicates
      (e.g. @(tsee tree-match-element-p))
      that take the grammar as a parameter.
      Given a grammar,
      one can define tree matching predicates
      that are specialized to the grammar,
      i.e. that implicitly depend on the grammar;
      one can also define operations on trees
      that are specialized to certain constructs of the grammar.")

    (xdoc::p
     "This @('deftreeops') macro automates the generation
      of these specialized tree matching predicates and operations,
      along with theorems about them.
      We plan to extend this @('deftreeops') macro
      to generate additional grammar-specific operations on trees,
      and theorems accompanying them."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(deftreeops *grammar*"
     "            :prefix ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('*grammar*')"
     (xdoc::p
      "Name of the constant that contains the grammar
       that the generated functions and theorems are specialized to.")
     (xdoc::p
      "This must be a symbol that is a named constant
       whose value is a grammar, i.e. a value of type @(tsee rulelist).
       It could be a grammar introduced by @(tsee defgrammar).")
     (xdoc::p
      "The grammar must be "
      (xdoc::seetopic "well-formedness" "well-formed")
      " and "
      (xdoc::seetopic "closure" "closed")
      "."))

    (xdoc::desc
     "@(':prefix') &mdash; no default"
     (xdoc::p
      "Specifies the prefix for the specialized tree operations.")
     (xdoc::p
      "It must be a symbol in a package different from
       the Common Lisp package and the keyword package.")
     (xdoc::p
      "A good choice for this symbol could be @('<p>::cst'),
       where @('<p>') is the package of the application at hand
       and where @('cst') stands for CST (Concrete Syntax Tree).
       If the application involves multiple grammars for different languages,
       a good choice for this symbol could be @('<p>::<lang>-cst'),
       where @('<lang>') indicates the language that the grammar refers to.")
     (xdoc::p
      "In the rest of this documentation page,
       let @('<prefix>') be this symbol.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::p
     "The events are put in a @(tsee defsection)
      whose name is @('*grammar*-tree-operations')
      (i.e. the symbol obtained by adding @('-tree-operations')
      to the name of the constant whose value is the grammar),
      and whose only parent is the @('*grammar*') symbol.
      That is, the generated section is
      a sub-topic of the XDOC topic for the grammar.")

    (xdoc::desc
     (list
      "@('<prefix>-matchp')"
      "@('<prefix>-list-elem-matchp')"
      "@('<prefix>-list-rep-matchp')"
      "@('<prefix>-list-list-conc-matchp')"
      "@('<prefix>-list-list-alt-matchp')")
     (xdoc::p
      "Tree matching predicates, specialized to @('*grammar*').
       The predicates are put in the same package as @('<prefix>').")
     (xdoc::p
      "Each predicate takes two arguments:")
     (xdoc::ol
      (xdoc::li
       "A tree (for the first one),
        or a list of trees (for the second and third one),
        or a list of lists of trees (for the fourth and fifth one).")
      (xdoc::li
       "An ACL2 string, which must be an ABNF concrete syntax representation of
        an element (for the first and second one),
        or a repetition (for the third one),
        or a concatenation (for the fourth one),
        or an alternation (for the fifth one)."))
     (xdoc::p
      "Each predicate holds iff the (list of (list(s) of)) tree(s)
       is terminated and
       matches the element or repetition or concatenation or alternation.
       While in the @(see semantics) it makes sense
       to include non-terminated trees as potentially matching,
       for a specific grammar it normally makes sense
       to consider only terminated trees:
       this motivates the extra condition.")
     (xdoc::p
      "These generated predicates are actually macros,
       which use (subroutines of) the "
      (xdoc::seetopic "grammar-parser" "verified grammar parser")
      " to parse the ACL2 strings passed as second arguments
       into their ABNF abstract syntactic representation,
       and then expand to calls of the appropriate
       generic tree matching predicates in the @(see semantics),
       passing the grammar as argument to them;
       the dependency on the grammar is implicit in the generated predicates.
       Note that the parsing of the strings happens
       at macro expansion time (i.e. at compile time),
       not at predicate call time (i.e. at run time).")
     (xdoc::p
      "There are some generated internal intermediate predicates
       that these macros expand into calls of,
       and it is these intermediate predicates that call
       the generic tree matching predicates from the @(see semantics).
       These intermediate predicates are actual ACL2 functions,
       whose names are identical to the macros but with @('$') at the end. "
      (xdoc::seetopic "acl2::macro-aliases-table" "Macro aliases")
      " are also generated that link the macro names to the function names:
       this way, the predicates can be opened (in proofs)
       via their macro names."))

    (xdoc::desc
     "@('<prefix>-<rulename>-nonleaf')"
     (xdoc::p
      "For each rule name defined in the grammar:
       a theorem saying that a tree that matches the rule name
       is a non-leaf tree."))

    (xdoc::desc
     "@('<prefix>-<rulename>-rulename')"
     (xdoc::p
      "For each rule name defined in the grammar:
       a theorem saying that a tree that matches the rule name
       has exactly that rule name."))

    (xdoc::desc
     "@('<prefix>-<rulename>-branches-match-alt')"
     (xdoc::p
      "For each rule name defined in the grammar:
       a theorem saying that if a tree matches the rule name
       then its branches match the alternation that defines the rule name."))

    (xdoc::desc
     "@('<prefix>-<rulename>-concs')"
     (xdoc::p
      "For each rule name defined in the grammar:
       a theorem saying that
       if a list of lists of trees matches
       the alternation that defines the rule name
       then the list of lists of trees matches
       one of the concatenations in the alternation.
       This is a disjunctive theorem,
       unless the alternation consists of just one concatenation."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc-equivs')"
     (xdoc::p
      "For each rule name defined in the grammar
       by an alternation of two or more concatenations,
       such that each concatenation is
       a singleton of a singleton repetition of a rule name element:
       a theorem stating equivalences between
       (i) the branches (of a tree matching the rule name)
       matching each concatenation and
       (ii) some term over the branches
       that discriminates among the concatenations that define the rule name;
       there is an equivalence for each concatenation,
       and the theorem consists of the conjunction of the equivalences.
       This theorem is a conjunction of equivalences,
       one for each concatenation that defines the rule name."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc?')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations:
       a function that, given a tree matching the rule name,
       returns a positive integer
       indicating the concatenation matched by the subtrees,
       in the order in which the concatenation appears in the alternation,
       numbered starting from 1 for the first concatenation.
       If a rule name is defined by multiple rules
       (the first one non-incremental, the other ones incremental),
       the order of the concatenations
       indicated by the integer returned by this function
       is lexicographic, based first on the order of the rules
       and then on the order of the concatenations within each rule.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc?-possibilities'),
        which asserts that the result of the function is
        one of the numbers 1, ..., @('n'),
        where @('n') is the number of concatenations
        that form the alternation that defines the rule name.
        This is a disjunctive theorem.")
      (xdoc::li
       "@('<prefix>-<rulename>-conc?-<i>-iff-match-conc'),
        for each concatenation @('<i>') (numbered starting from 1)
        in the alternation that defines the rule name,
        which asserts that the function returns @('<i>')
        iff the subtrees match the concatenation.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of one concatenation:
       a function that, given a tree matching the rule name,
       returns the list of lists of subtrees of the tree.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc-match'),
        which asserts that the result of the function
        matches the concatenation.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc<i>')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations,
       such that each concatenation is
       a singleton of a singleton repetition of a rule name element,
       and for each concatenation @('<i>') (numbered starting from 1)
       in the alternation:
       a function that, given a tree matching the rule name
       whose subtrees match the concatenation @('<i>')
       (expressed via @('<prefix>-<rulename>-conc?') above),
       returns the list of lists of subtrees of the tree.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc<i>-match'),
        which asserts that the result of the function
        matches the concatenation @('<i>').")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc-matching')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of one concatenation,
       such that the concatenation consists of one repetition:
       a theorem saying that
       if a list of lists of trees matches that concatenation
       then the list of lists of trees has the same length as the concatenation
       and each list of trees matches
       the corresponding repetition of the concatenation."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc<i>-matching')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations,
       and for each concatenation @('<i>') (numbered starting from 1)
       in the alternation,
       such that the concatenation consists of one repetition:
       a theorem saying that
       if a list of lists of trees matches that concatenation
       then the list of lists of trees has the same length as the concatenation
       and each list of trees matches
       the corresponding repetition of the concatenation."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc-rep')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of one concatenation,
       such that the concatenation consists of one repetition:
       a function that, given a tree matching the rule name,
       returns the list of trees corresponding to the repetition.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc-rep-match'),
        which asserts that the result of the function
        matches the repetition.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc<i>-rep')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations,
       and for each concatenation @('<i>') (numbered starting from 1)
       in the alternation,
       such that the concatenation consists of one repetition:
       a function that, given a tree matching the rule name,
       returns the list of trees corresponding to the repetition.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc<i>-rep-match'),
        which asserts that the result of the function
        matches the repetition.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc-rep-matching')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of one concatenation,
       such that the concatenation consists of one repetition,
       such that the repetition has a range of 1:
       a theorem saying that
       if a list of trees matches that repetition
       then the list of trees has a length
       within the range of the repetition
       and each tree matches
       the element of the repetition."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc<i>-rep-matching')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations,
       and for each concatenation @('<i>') (numbered starting from 1)
       in the alternation that defines the rule name,
       such that the concatenation consists of one repetition,
       such that the repetition has a range of 1:
       a theorem saying that
       if a list of trees matches that repetition
       then the list of trees has a length
       within the range of the repetition
       and each tree matches
       the element of the repetition."))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc-rep-elem')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of one concatenation,
       such that the concatenation consists of one repetition,
       such that the repetition has a range of 1,
       and such that the element of the repetition is a rule name:
       a function that, given a tree matching the rule name,
       returns the tree corresponding to the element of the repetition.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc<i>-rep-elem-match'),
        which asserts that the result of the function
        matches the rule name of the element.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function.")))

    (xdoc::desc
     "@('<prefix>-<rulename>-conc<i>-rep-elem')"
     (xdoc::p
      "For each rule name defined in the grammar by
       an alternation of two or more concatenations,
       and for each concatenation @('<i>') (numbered starting from 1)
       in the alternation,
       such that the concatenation consists of one repetition,
       such that the repetition has a range of 1,
       and such that the element of the repetition is a rule name:
       a function that, given a tree matching the rule name,
       returns the tree corresponding to the element of the repetition.
       The generated function is accompanied by the following theorems:")
     (xdoc::ul
      (xdoc::li
       "@('<prefix>-<rulename>-conc<i>-rep-elem-match'),
        which asserts that the result of the function
        matches the rule name of the element.")
      (xdoc::li
       "@(tsee fty::deffixequiv) theorems for the function."))))))
