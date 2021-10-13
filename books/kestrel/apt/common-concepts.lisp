; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/defxdoc-plus" :dir :system)

; (depends-on "design-notes/specs-refs.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ common-concepts
  :parents (apt)
  :short "Concepts that are common to different APT transformations."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc redundancy
  :short "Notion of redundancy for APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A call of an APT transformation is redundant if and only if
     it is identical to a previous successful call of the same transformation
     whose @(':show-only') input is not @('t'),
     except that the two calls may differ in
     their @(':print') and @(':show-only') inputs.
     These options do not affect the generated events,
     and thus they are ignored for the purpose of redundancy.")
   (xdoc::p
    "A call of an APT transformation whose @(':show-only') input is @('t')
     does not generate any event.
     No successive call may be redundant with such a call.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-name-generation
  :short "How APT transformations generate function names."
  :long
  (xdoc::topstring
   (xdoc::p
    "APT transformations generate transformed functions from existing functions.
     The names of the generated functions may be specified explicitly,
     or may be automatically generated from the names of the existing functions,
     according to some rules.
     Certain APT transformations do that according to the rules described here.
     These rules apply only to the APT transformations
     whose user documentation explicitly references this XDOC topic.")
   (xdoc::p
    "The name generation rules described here are based on "
    (xdoc::seetopic "acl2::numbered-names" "numbered names")
    ": see their topic first.
     Roughly speaking, the application of an APT transformation
     to a target function whose name is a numbered name
     generates a new function with the next numbered name,
     i.e. the numbered name with the same base as the target function
     and with the smallest index greater than the one of the target function
     that makes the new function's name fresh, i.e. valid for a new function.
     Such an index is often one plus the index of the target function,
     but in general it may be larger if that name already happens to exist
     (which would not be a recommended way to organize an APT derivation,
     but cannot be prevented in general).
     If the target function name is not actually a numbered name,
     for the purpose of generating a function with the next numbered name,
     the non-existent index of the target function name is regarded to be 0;
     thus, the next numbered name has often index 1 in this case.")
   (xdoc::p
    "Certain APT transformations, when applied to a target function,
     generate a single new function.
     These transformations have a @(':new-name') input, which is
     either @(':auto') (the default) to specify automatic name generation,
     or an explicitly specified symbol to use for the new function.
     When the @(':new-name') input is @(':auto'),
     the name of the new function is determined
     just as explained in the previous paragraph.")
   (xdoc::p
    "Certain APT transformations may generate, besides the new function,
     also an additional wrapper function,
     This happens when the new function has different arguments
     (different in number and/or in types)
     from the target function:
     the wrapper function has
     the same number and types of arguments as the target function,
     and calls the new function with suitable arguments,
     i.e. it ``wraps'' the new function to match the old function,
     ``bridging'' between the two sets of arguments.
     The wrapper function is optional:
     these transformations have a @(':wrapper') boolean input
     that specifies whether the wrapper function is generated (@('t'))
     or not (@('nil'), the default).
     When the @(':wrapper') input is @('nil'),
     only the new function is generated,
     and when the @(':new-name') input is @(':auto')
     its name is again generated as explained above.")
   (xdoc::p
    "If instead the @(':wrapper') input is @('t'),
     then another input of the transformation, @(':wrapper-name'),
     becomes relevant
     (this input may be present only if @(':wrapper') is @('t')).
     Similarly to @(':new-name'), also @(':wrapper-name') may be
     either @(':auto') to specify automatic name generation,
     or a symbol to use as the wrapper function name.
     Note that it is possible for
     just one of @(':new-name') and @(':wrapper-name') to be @(':auto'),
     not necessarily both.
     The rules for automatic name generation are as follows:")
   (xdoc::ul
    (xdoc::li
     "If neither @(':new-name') nor @(':wrapper-name') is @(':auto'),
      then there is actually no automatic name generation.")
    (xdoc::li
     "If @(':new-name') is @(':auto') but @(':wrapper-name') is not,
      the name of the new function is determined as above,
      with the additional constraint that the new index must be such that
      the resulting name is distinct from
      the explicitly specified wrapper function name.
      In a well-structured APT derivation,
      this additional constraint is expected to be normally satisfied
      by one plus the index of the target function.")
    (xdoc::li
     "If @(':wrapper-name') is @(':auto') but @(':new-name') is not,
      the rules are the same as the previous case,
      but with the roles of the new and wrapper function names swapped.
      That is, the wrapper function name is a numberd name
      whose base is the same as the target function,
      and whose index is the smallest one that is
      greater than the index of the target function
      and also distinct from the explicitly specified new function name.")
    (xdoc::li
     "If both @(':new-name') and @(':wrapper-name') are @(':auto'),
      then both the new and wrapper function names are numbered names,
      determined as follows.
      The base of the new function's name is
      the concatenation of the target function's name followed by @('-aux').
      The base of the wrapper function's name is
      the same as the target function's name.
      The index of both new and wrapper function names is the smallest one
      that is greater than the one of the target function
      and that makes both the new and wrapper function names fresh.
      In well-structured APT derivations,
      this index is normally expected to be
      just one plus the target function's index."))
   (xdoc::p
    "The @('-aux') in the new function name in the last case above
     means `auxiliary', which is a common naming convention
     for the ``loop'' of a function (in this case, the non-wrapper
     function).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *specs-refs-design-notes*
  (xdoc::&& "`Specifications and Refinements' "
            (xdoc::ahref "res/kestrel-apt-design-notes/specs-refs.pdf"
                         "design notes")))

(defxdoc specification-forms

  :short "Forms of specifications handled by certain APT transformations."

  :long

  (xdoc::topstring

   (xdoc::p
    "Certain APT transformations operate on specifications
     that are shallow pop-refinement predicates
     as described in the "
    *specs-refs-design-notes*
    ", which use "
    (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
    ". Currently these second-order predicates
     must be expressed using " (xdoc::seetopic "soft::soft" "SOFT") ".
     In the future, the transformations may be extended
     to operate on second-order predicates
     expressed using the built-in @(tsee apply$).")

   (xdoc::p
    "In this manual page,
     we define and name certain specific forms of such SOFT specifications.
     In the " *specs-refs-design-notes* ", these forms are shown
     in Section `Some Shallow Pop-Refinement Specification Forms'.
     APT transformations that operate on these forms
     reference this manual page from their user documentation pages,
     along with a designation of the form.")

   (xdoc::h3 "Pre/Post-Condition")

   (xdoc::p
    "This form is denoted by @($PP$) in the " *specs-refs-design-notes* ".")

   (xdoc::p
    "A specification of this form is a SOFT quantifier function
     (see `Classification' section in @(tsee soft::defsoft))
     that has no parameters,
     that depends on one function variable (call it @('?f')),
     and whose body has the form")
   (xdoc::codeblock
    "(forall (x1 ... xn)"
    "        (implies (pre x1 ... xn)"
    "                 (post x1 ... xn (?f x1 ... xn))))")
   (xdoc::p
    "where @('n') is 1 or more,
     @(tsee implies) may be @('impliez') instead,
     @('pre') is a precondition predicate, and
     @('post') is a postcondition predicate.
     Note that @('?f') returns a single result (not @(tsee mv)),
     because SOFT function variables currently always do.")

   (xdoc::p
    "This is a typical specification consisting of
     a precondition on the inputs and
     a postcondition on the output (and inputs).")

   (xdoc::p
    "In the " *specs-refs-design-notes* ",
     the specification is denoted by @($S$),
     @('?f') is denoted by @($f$),
     @('x1'), ..., @('xn') are denoted by a single @($x$)
     (the generalization to multiple variable is obvious),
     @('pre') is denoted by @($\\Phi$), and
     @('post') is denoted by @($\\Psi$).")

   (xdoc::h3 "Input/Output Relation")

   (xdoc::p
    "This form is denoted by @($Rf$) in the " *specs-refs-design-notes* ".")

   (xdoc::p
    "A specification of this form is a SOFT quantifier function
     (see `Classification' section in @(tsee soft::defsoft))
     that has no parameters,
     that depends on one function variable (call it @('?f')),
     and whose body has the form")
   (xdoc::codeblock
    "(forall (x1 ... xn)"
    "        iorel<x1,...,xn,(?f x1 ... xn)>)")
   (xdoc::p
    "where @('n') is 1 or more,
     @('iorel<...>') is a term that depends on the quantified variables
     and that contains a single occurrence of
     a call of @('?f') on the quantified variables.")

   (xdoc::p
    "The predicate @('(lambda (x1 ... xn y) iorel<x1,...,xn,y>)')
     is a relation between the inputs @('x1'), ..., @('xn')
     and the output @('y').
     This is a more general form than the pre/post-condition form @($PP$),
     which it subsumes.")

   (xdoc::p
    "In the " *specs-refs-design-notes* ",
     the specification is denoted by @($S$),
     @('?f') is denoted by @($f$),
     @('x1'), ..., @('xn') are denoted by a single @($x$)
     (the generalization to multiple variable is obvious), and
     @('(lambda (x1 ... xn y) iorel<x1,...,xn>)') is denoted by @($R$).")

   (xdoc::h3 "Input/Output Relation with Selected Input and Modified Inputs")

   (xdoc::p
    "This form is denoted by @($Rf\\alpha$) in the "
    *specs-refs-design-notes* ".")

   (xdoc::p
    "A specification of this form is a SOFT quantifier function
     (see `Classification' section in @(tsee soft::defsoft))
     that has no parameters,
     that depends on one function variable (call it @('?f')),
     and whose body has the form")
   (xdoc::codeblock
    "(forall (x x1 ... xn)"
    "        iorel<x,x1,...,xn,(?f x a1<x1,...,xn> ... am<x1,...,xn>)>)")
   (xdoc::p
    "where @('n') may be 0 and
     @('iorel<...>') is a term that depends on the quantified variables
     and that contains a single occurrence of
     a call of @('?f') of the form shown above,
     where @('m') may be 0 and
     each @('aj<x1,...,xn>') is a term that depends on @('x1'), ..., @('xn')
     (and must not depend on @('x')).
     The variable @('x') does not actually have to be
     the first quantified variable in the list after @('forall')
     and the first argument of the call of @('?f'):
     it may be anywhere in the list and in any argument position,
     as it is identified in same way by the APT transformations;
     to ease exposition, in the documentation pages of the APT transformations,
     we assume that it is the first one, as shown above.")

   (xdoc::p
    "This form generalizes the plain input/output relation form @($Rf$),
     because some of the inputs (namely @('x1'), ..., @('xn'))
     are modified to become the terms @('aj<x1,...,xn>')
     before @('?f') is applied to them;
     in addition, one input (namely @('x')) is selected
     and not subjected to that modification.
     Thus, the input/output relation
     @('(lambda (x x1 ... xn y) iorel<x,x1,...,xn,y>)')
     is applied, as the output,
     not to a call of @('?f') directly on
     the inputs @('x'), @('x1'), ..., @('xn'),
     but to a call of @('?f') on
     the inputs @('x'), @('a1<x1,...,xn>'), ..., @('am<x,x1,...,xn>').
     When @('m') is @('n') and each @('aj<x1,...,xn>') is @('xj'),
     this form is the same as the plain input/output form @($Rf$).")

   (xdoc::p
    "In the " *specs-refs-design-notes* ",
     the specification is denoted by @($S$),
     @('?f') is denoted by @($f$),
     @('x') is denoted by @($x$),
     @('x1'), ..., @('xn') are denoted by @($\\overline{x}$),
     @('a1<x1,...,xn>'), ..., @('am<x1,...,xn>') are denoted by
     @($\\overline{\\alpha}(\\overline{x})$), and
     @('(lambda (x x1 ... xn y) iorel<x,x1,...,xn,y>)')
     is denoted by @($R$).")))
