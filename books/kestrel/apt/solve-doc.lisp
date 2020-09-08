; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "utilities/xdoc-constructors")

; (depends-on "design-notes/solve.pdf")
; (depends-on "kestrel/design-notes/notation.pdf" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *solve-design-notes*
  (xdoc::&& "@('solve') "
            (xdoc::ahref "res/kestrel-apt-design-notes/solve.pdf"
                         "design notes")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc solve

  :parents (apt)

  :short "APT solving transformation:
          directly determine a solution to a specification."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "Program synthesis, i.e. deriving a program from a specification,
      can be viewed as a form of constraint solving:
      the specification expresses the constraints,
      and the synthesized program is a solution to the constraints.
      In some cases,
      this kind of constraint satisfaction problem can be solved directly,
      e.g. via inference techniques.
      This transformation attempts to solve a specification directly,
      producing a satisfying program if successful.")

    (xdoc::p
     "A specification is a predicate over target programs,
      so that a solution to a specification is indeed a program.
      The programs may be deeply or shallowly embedded in the ACL2 logic,
      according to the "
     (xdoc::ahref "https://www.isa-afp.org/entries/Pop_Refinement.html"
                  "pop-refinement")
     " and "
     (xdoc::ahref "http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3"
                  "shallow pop-refinement")
     " approaches, respectively.
      Currently, this solving transformation operates on
      specifications over shallowly embedded programs,
      i.e. second-order predicates in ACL2.
      Currently, this solving transformation expects
      these predicates to be expressed using "
     (xdoc::seetopic "soft::soft" "SOFT")
     ", but the transformation may be extended, in the future,
      to operate on second-order predicates expressed via
      the built-in @(tsee apply$).")

    (xdoc::p
     "A range of direct solving methods may be employed:
      rewriting,
      narrowing (i.e. computing sufficient conditions),
      witness finding via resolution,
      SMT solving,
      SAT solving,
      etc.
      Currently this solving transformation only supports (a form of) rewriting,
      but there are plans to extend it to additional methods.
      Note that some of the methods listed above
      correspond to the sketching approach to program synthesis,
      which can therefore be a valuable tool in APT's arsenal.")

    (xdoc::p
     "This transformation also supports a manual solving method,
      in which the user provides the solution,
      possibly with hints to prove its correctness.
      While this is not an automatic method like the ones described above,
      it may be useful when the automatic methods fail,
      or when the solution happens to be simple to find and to prove.
      Using this transformation with the manual solving method
      is generally more convenient than writing out the full refinement step:
      in particular, this transformation automates
      the generation and proof of the refinement theorem
      (i.e. that the new specification implies the old one)
      from the proof that the manually provided solution
      satisfies the (old) specification.")

    (xdoc::p
     "Solving methods that require tools that are not part of ACL2
      can be modularly and selectively loaded and used
      by including the files in which their core implementation lies.
      This solving transformation, as part of input validation,
      checks that (the file of) the specified solving method has been loaded
      (more precisely, it checks that a function symbol in that file
      is present in the ACL2 world).")

    (xdoc::p
     "The " *solve-design-notes* ", which use "
     (xdoc::a :href "res/kestrel-design-notes/notation.pdf" "this notation")
     ", provide the mathematical concepts and template proofs
      upon which this transformation is based.
      These notes should be read alongside this reference documentation,
      which refers to them in some places."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form
    (xdoc::codeblock
     "(solve old"
     "       :method                 ; no default"
     "       :method-rules           ; default nil"
     "       :solution-name          ; default :auto"
     "       :solution-enable        ; default nil"
     "       :solution-guard         ; default t"
     "       :solution-guard-hints   ; default nil"
     "       :solution-body          ; no default"
     "       :solution-hints         ; default nil"
     "       :new-name               ; default :auto"
     "       :new-enable             ; default :auto"
     "       :old-if-new-name        ; default from table"
     "       :old-if-new-enable      ; default from table"
     "       :verify-guards          ; default :auto"
     "       :print                  ; default :result"
     "       :show-only              ; default nil"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc-apt-input-old
     (xdoc::p
      "@('old') must be a SOFT quantifier function
       (see `Classification' section in @(tsee soft::defsoft))
       that depends on one function variable (call it @('?f')),
       that has no parameters,
       and whose body has the form")
     (xdoc::codeblock
      "(forall (x1 ... xn) matrix<(?f x1 ... xn)>)")
     (xdoc::p
      "where @('x1'), ..., @('xn') are 0 or more variables
       and @('matrix<(?f x1 ... xn)>') is a term
       that contains a single call of @('?f') on @('x1'), ..., @('xn')
       (after translation and @(tsee let) expansion).")
     (xdoc::p
      "The transformation attempts to solve for @('?f'),
       i.e. to determine an @('n')-ary function
       that satisfies the constraints that @('old') puts on @('?f').")
     (xdoc::p
      "In the " *solve-design-notes* ",
       @('old') is denoted by @($S$),
       @('?f') is denoted by @($f$),
       @('x0'), ..., @('xn') are denoted by the single variable @($x$)
       (the generalization to multiple variables
       is straighforward in the design notes), and
       @('matrix<(?f x1 ... xn)>') is denoted by @($R(x,f(x))$)."))

    (xdoc::desc
     "@(':method') &mdash; no default"
     (xdoc::p
      "Specifies the solving method to use.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':axe-rewriter'), to use the Axe rewriter.
        (Until Axe is open-sourced in the community books,
        this method is only available inside Kestrel.)")
      (xdoc::li
       "@(':manual'), to manually supply a solution."))
     (xdoc::p
      "Support for more methods is planned."))

    (xdoc::desc
     "@(':method-rules') &mdash; @('nil')"
     (xdoc::p
      "Specifies the Axe rewrite rules to use
       when @(':method') is @(':axe-rewriter').")
     (xdoc::p
      "It must be a list of symbols that are
       names of ACL2 theorems usable as Axe rewrite rules.")
     (xdoc::p
      "This input may be present only if @(':method') is @(':axe-rewriter')."))

    (xdoc::desc
     "@(':solution-name') &mdash; default @(':auto')"
     (xdoc::p
      "Determines the name of the generated solution function for @('?f').")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), which may only be used
        when the name of @('?f') starts with a @('?').
        In this case, the name of the solution is the symbol obtained
        by removing the initial @('?') from the name of @('?f').")
      (xdoc::li
       "Any other symbol, to use as the name of the solution function."))
     (xdoc::p
      "In the rest of the documentation page,
       let @('f') be this name."))

    (xdoc::desc
     "@(':solution-enable') &mdash; default @('nil')"
     (xdoc::p
      "Determines whether @('f') is enabled.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to enable it.")
      (xdoc::li
       "@('nil'), to disable it.")))

    (xdoc::desc
     "@(':solution-guard') &mdash; default @('t')"
     (xdoc::p
      "Determines the guard of @('f').")
     (xdoc::p
      "It must be an untranslated term
       whose free variables are among @('x1'), ..., @('xn').
       The term must return a single (i.e. non-@(tsee mv)) result.")
     (xdoc::p
      "See Section `Solution Determination' below
       for a discussion about this input."))

    (xdoc::desc
     "@(':solution-guard-hints') &mdash; default @('nil')"
     (xdoc::p
      "Determines the hints to verify the guards of @('f').")
     (xdoc::p
      "See Section `Solution Determination' below
       for a discussion about this input.")
     (xdoc::p
      "This input may be present only if guards are to be verified,
       as determined by the @(':verify-guards') input."))

    (xdoc::desc
     "@(':solution-body') &mdash; no default"
     (xdoc::p
      "Specifies the body of the solution function,
       when @(':method') is @(':manual').")
     (xdoc::p
      "It must be an untranslated term
       whose free variables are among @('x1'), ..., @('xn').
       The term must return a single (i.e. non-@(tsee mv)) result.")
     (xdoc::p
      "See Section `Solution Determination' below
       for a discussion about this input.")
     (xdoc::p
      "This input may be present only if @(':method') is @(':manual').
       In fact, this input must be present if @(':method') is @(':manual')."))

    (xdoc::desc
     "@(':solution-hints') &mdash; @('nil')"
     (xdoc::p
      "Specifies the hints to prove the correctness of the solution,
       when @(':method') is @(':manual').")
     (xdoc::p
      "It must be an untranslated term
       whose free variables are among @('x1'), ..., @('xn').")
     (xdoc::p
      "See Section `Solution Determination' below
       for a discussion about this input.")
     (xdoc::p
      "This input may be present only if @(':method') is @(':manual')."))

    (xdoc::desc-apt-input-new-name)

    (xdoc::desc-apt-input-new-enable)

    (xdoc::desc-apt-input-old-if-new-name)

    (xdoc::desc-apt-input-old-if-new-enable)

    (xdoc::desc
     "@(':verify-guards') &mdash; default @(':auto')"
     (xdoc::p
      "Determines whether the guards of the generated function(s)
       are to be verified or not.")
     (xdoc::p
      "It must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to verify them.")
      (xdoc::li
       "@('nil'), to not verify them.")
      (xdoc::li
       "@(':auto'), to verify them if and only if
        the guards of @('old') are verified.")))

    (xdoc::evmac-input-print solve)

    (xdoc::evmac-input-show-only solve))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Solution Determination")

   (xdoc::p
    "The transformation attempts to find a solution for @('?f')
     according to the chosen method, as explained below.
     A solution may or may not be found.
     If no solution is found, the transformation fails
     with an informative error message.")

   (xdoc::h4 "Axe Rewriter")

   (xdoc::p
    "When the @(':method') input is @(':axe-rewriter'),
     the transformation calls the Axe rewriter
     on the term @('matrix<(?f x1 ... xn)>'),
     obtaining a rewritten term @('result').")

   (xdoc::p
    "When @('result') has the form")
   (xdoc::codeblock
    "(equal (?f x1 ... xn) term<x1,...,xn>)")
   (xdoc::p
    "where @('term<x1,...,xn>') is a term
     that may depend on @('x1'), ..., @('xn')
     and that does not contain @('?f'),
     the transformation is successful,
     and the determined solution is")
   (xdoc::codeblock
    "(defun f (x1 ... xn)"
    "  term<x1,...,xn>)")
   (xdoc::p
    "Note that there is no general guarantee that
     @('term<x1,...,xn>') can be guard-verified
     without assumptions on @('x1'), ..., @('xn').
     The @(':solution-guard') input may be used to add such assumptions,
     and @(':solution-guard-hints') input may be used to verify guards,
     but there is no general guarantee that suitable input values always exist:
     the Axe rewriter may produce a logically valid term
     that cannot be guard-verified under any hypotheses on its variables.
     Future extensions of this transformation may address this issue,
     e.g. by limiting rewriting so that
     only guard-verifiable terms are produced.")

   (xdoc::p
    "When @('result') is @('t'),
     the transformation is successful,
     and the determined solution is")
   (xdoc::codeblock
    "(defun f (x1 ... xn)"
    "  nil)")
   (xdoc::p
    "The fact that @('matrix<(?f x1 ... xn)>') rewrote to @('t')
     means that any @('?f') satisfies the constraints.
     So anything can be used as the solution @('f').
     We use the function that always returns @('nil') for simplicity.
     While this may seem an unlikely case,
     it may arise under certain conditions,
     e.g. for some boundary conditions.")

   (xdoc::p
    "Otherwise, if @('result') is anything else than the forms above,
     the transformation fails.
     No solution has been determined.")

   (xdoc::p
    "When the transformation is successful,
     the Axe rewriting provides an Axe proof of correctness of the solution.
     This should suffice to generate an ACL2 proof
     of the @('old-if-new') refinement theorem in principle,
     but in practice there may be technical difficulties in some cases.
     Future extensions of this transformation may address this issue,
     e.g. by having the Axe rewriter produce an ACL2 proof in some form
     that this transformation may use to prove the refinement theorem.")

   (xdoc::p
    "In any case, the transformation attempts to prove a theorem
     to confirm the correctness of Axe's rewriting in ACL2.
     If that theorem is successful,
     the transformation internally generates a theorem of the form")
   (xdoc::codeblock
    "(implies (equal (?f x1 ... xn)"
    "                term<x1,...,xn>)"
    "         matrix<(?f x1 ... xn)>)")
   (xdoc::p
    "which essentially says that the matrix of @('old')
     if we replace @('(?f x1 ... xn)') with @('term<x1,...,xn>'),
     i.e. that the inferred solution body satisfies the initial specification.
     It is the latter theorem that is used to prove @('old-if-new').
     Its formulation is equivalent to @('matrix<term<x1,...,xn>>'),
     but the formulation used is more convenient
     for generating the proof of @('old-if-new').")

   (xdoc::h4 "Manual")

   (xdoc::p
    "When the @(':method') input is @(':manual'),
     the transformation calls no inference tool.
     Instead, the @(':solution-body') input, which must be supplied,
     is used to determine the solution")
   (xdoc::codeblock
    "(defun f (x1 ... xn)"
    "  term<x1,...,xn>)")
   (xdoc::p
    "where @('term<x1,...,xn>') is the @(':solution-body') input;
     it is a term whose free variables are among @('x1'), ..., @('xn').")
   (xdoc::p
    "It must be the case that")
   (xdoc::codeblock
    "(implies (equal (?f x1 ... xn)"
    "                term<x1,...,xn>)"
    "         term<(?f x1 ... xn)>)")
   (xdoc::p
    "which has the same form as the one for the Axe rewriter (see above).
     Its proof is attempted via the @(':solution-hints') input.")
   (xdoc::p
    "The guard of @('f') is determined by @(':solution-guard').
     If guards are to be verified,
     the verification of the guards of @('f')
     are attempted using @(':solution-guard-hints').")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('f')"
     (xdoc::p
      "The solution for @('?f').")
     (xdoc::codeblock
      "(defun f (x1 ... xn)"
      "  (declare (xargs :guard ...)) ; from :solution-guard input"
      "  ...) ; see section 'Solution Determination' above")
     (xdoc::p
      "In the " *solve-design-notes* ",
       @('f') is denoted by @($f_0$)."))

    (xdoc::desc
     "@('new')"
     (xdoc::p
      "Specification strengthened by choosing the solution,
       i.e. equality between @('?f') and @('f'):")
     (xdoc::codeblock
      "(soft::defun-sk2 new ()"
      "  (forall (x1 ... xn)"
      "          (equal (?f x1 ... xn)"
      "                 (f x1 ... xn))))")
     (xdoc::p
      "In the " *solve-design-notes* ",
       @('new') is denoted by @($S'$)."))

    (xdoc::desc
     "@('old-if-new')"
     (xdoc::p
      "Theorem asserting that @('new') implies @('old')
       (i.e. a refinement relation):")
     (xdoc::codeblock
      "(defthm old-if-new"
      "  (implies (new)"
      "           (old))")
     (xdoc::p
      "In the " *solve-design-notes* ",
       @('old-if-new') is denoted by @($SS'$).")))))
