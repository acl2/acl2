; Arbitrary Recursion Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defarbrec

  :parents (kestrel-utilities)

  :short "Introduce an arbitrarily recursive function."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Given a recursive program-mode function
     that only calls logic-mode functions (besides calling itself)
     and that may not terminate,
     it is possible (under some conditions)
     to construct a logic-mode ``version'' of that function
     by explicitly testing for termination, via a non-executable predicate.
     The resulting logic-mode function is ``equivalent''
     to the program-mode function when the latter terminates.")

   (xdoc::p
    "The resulting logic-mode function can be subjected to
     formal verification and "
    (xdoc::seetopic "apt::apt" "transformation")
    ". In particular, if it can be proved that
     the termination test holds on every argument value,
     then the termination test can be transformed away
     (e.g. via a simplification transformation),
     obtaining a simpler, provably equivalent logic-mode function,
     which may be executable
     if the initial program-mode function was executable.
     If termination can be proved only on some argument values instead,
     the domain of the function can be restricted to those values
     (e.g. via @(tsee apt::restrict)),
     and then the termination test can be transformed away
     in the restricted domain.")

   (xdoc::p
    "Constructing the logic-mode function with the explicit termination test
     may be useful in program verification.
     The starting program-mode function could be the object of verification,
     or it may represent, in ACL2,
     a recursive or iterative program (fragment), in some programming language,
     that is the object of verification.
     Instead of having to prove termination right away
     in order to make the function amenable to any formal verification in ACL2,
     constructing a logic-mode function with an explicit termination test
     enables the ``deferral'' of the termination proof.
     The termination of certain programs may depend on
     fairly deep semantic properties of the programs
     (to the point of being inter-related with functional correctness):
     in these cases,
     it may be natural to prove these properties along with termination,
     instead of having to prove termination alone first.")

   (xdoc::p
    "The @('defarbrec') macro
     (for `<b>def</b>ine <b>arb</b>itrary <b>rec</b>ursion')
     constructs the logic-mode function with the explicit termination test,
     from a specified program-mode function.
     The program-mode function is specified as
     a name, a list of arguments, and a body (as in @(tsee defun)):
     @('defarbrec') constructs the program-mode function on the fly,
     uses it to construct the logic-mode function,
     which has the same name and arguments,
     discards the program-mode function
     (absent from the @(see world) after @(tsee defarbrec) completes),
     and retains the logic-mode function
     (present in the @(see world) after @(tsee defarbrec) completes).")

   (xdoc::p
    "The current implementation only works
     with program-mode functions that make one recursive call
     (so in this sense it does not support truly arbitrary recursion,
     but the `arbitrary' here refers to avoiding to prove termination),
     but it should be possible to extend the macro to handle functions that
     make multiple different recursive calls.
     The current implementation does not support guards yet,
     but it should be possible to add suitable support.")

   (xdoc::p
    "The fact that the program-mode function is constructed by @(tsee defarbrec)
     ensures that it satisfies certain well-formedness constraints,
     e.g. calling only existing functions
     with arguments whose numbers match the functions' arities.
     This ensures that the generated logic-mode function
     satisfies the same well-formedness constraints.")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defarbrec fn (x1 ... xn)"
    "  body"
    "  :update-names    ...  ; default nil"
    "  :terminates-name ...  ; default nil"
    "  :measure-name    ...  ; default nil"
    "  :nonterminating  ...  ; default :nonterminating"
    "  :print           ...  ; default :result"
    "  :show-only       ...  ; default nil"
    "  )")

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('fn')"
    (xdoc::p
     "Name of the function to introduce.")
    (xdoc::p
     "This is as in @(tsee defun)."))

   (xdoc::desc
    "@('x1 ... xn')"
    (xdoc::p
     "Formal arguments of the function to introduce.")
    (xdoc::p
     "These are as in @(tsee defun),
      but in addition they must not include any"
     (xdoc::seetopic "acl2::stobj" "stobjs")
     "."))

   (xdoc::desc
    "@('body')"
    (xdoc::p
     "Body of the program-mode function;
      the logic-mode function has a body based on this one.")
    (xdoc::p
     "This is as in @(tsee defun),
      but with the following additional constraints.")
    (xdoc::p
     "The program-mode function must
      contain a single recursive call,
      only call logic-mode functions (besides itself),
      return a non-" (xdoc::seetopic "mv" "multiple") " value, and
      have no input or output " (xdoc::seetopic "acl2::stobj" "stobjs") ".")
    (xdoc::p
     "In the rest of this documentation page, for expository convenience,
      it is assumed that the program-mode function has the following form:")
    (xdoc::codeblock
     "(defun fn (x1 ... xn)"
     "  (if test<x1,...,xn>"
     "      base<x1,...,xn>"
     "    combine<x1,...,xn,(fn update-x1<x1,...,xn>"
     "                          ..."
     "                          update-xn<x1,...,xn>)>))"))

   (xdoc::desc
    "@(':update-names') &mdash; default @('nil')"
    (xdoc::p
     "Determines the names of the generated iterated argument update functions,
      i.e. the functions that iterate the updates of the arguments
      in the recursive call of the program-mode function
      (see the `Generated Functions' section below).")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to use, for each argument @('xi'):
       @('fn'),
       followed by @('-'),
       followed by @('xi'),
       followed by @('*');
       the symbols are in the same package as @('fn').")
     (xdoc::li
      "A @('nil')-terminated list of @('n') distinct symbols
       (that are not in the main Lisp package and that are not keywords),
       to use as the names of the functions."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('update*-x1'), ..., @('update*-xn') be
      the names of these functions."))

   (xdoc::desc
    "@(':terminates-name') &mdash; default @('nil')"
    (xdoc::p
     "Determines the name of the generated predicate
      that tests whether the program-mode function terminates.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to use @('fn') followed by @('-terminates');
       the symbol is in the same package as @('fn').")
     (xdoc::li
      "Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the predicate."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('terminates') be the name of this predicate."))

   (xdoc::desc
    "@(':measure-name') &mdash; default @('nil')"
    (xdoc::p
     "Determines the name of the generated measure function
      of the logic-mode function.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to use @('fn') followed by @('-measure');
       the symbol is in the same package as @('fn').")
     (xdoc::li
      "Any other symbol
       (that is not in the main Lisp package and that is not a keyword),
       to use as the name of the measure function."))
    (xdoc::p
     "In the rest of this documentation page,
      let @('measure') be the name of this function."))

   (xdoc::desc
    "@(':nonterminating') &mdash; default @(':nonterminating')"
    (xdoc::p
     "Specifies the value that the logic-mode function returns
      when the program-mode function does not terminate.")
    (xdoc::p
     "It must be a term
      that includes no free variables other than @('x1'), ..., @('xn'),
      that only calls logic-mode functions,
      that returns a non-" (xdoc::seetopic "mv" "multiple") " value,
      and that has no output " (xdoc::seetopic "acl2::stobj" "stobjs") ".")
    (xdoc::p
     "In the rest of this documentation page,
      let @('nonterminating') be this term."))

   (xdoc::desc
    "@(':print') &mdash; default @(':result')"
    (xdoc::p
     "Customizes the screen output.")
    (xdoc::p
     "It must be one of the following:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to print nothing.")
     (xdoc::li
      "@(':error'), to print only error output.")
     (xdoc::li
      "@(':result'), to print, besides error output,
       the functions described in the `Generated Functions' section below,
       i.e. the result of @(tsee defarbrec).")
     (xdoc::li
      "@(':all'), to print,
       besides error output and the result (see @(':result') above),
       ACL2's output in response to all the submitted events
       (the ones that form the result as well as some ancillary ones)."))
    (xdoc::p
     "If the call to @('defarbrec') is redundant
      (see the `Redundancy' section below),
      a message to that effect is printed on the screen,
      unless @(':print') is @('nil')."))

   (xdoc::desc
    "@(':show-only') &mdash; default @('nil')"
    (xdoc::p
     "Determines whether the event expansion of @('defarbrec')
     is submitted to ACL2 or printed on the screen:")
    (xdoc::ul
     (xdoc::li
      "@('nil'), to submit it.")
     (xdoc::li
      "@('t'), to print it.
       In this case:
       the event expansion is printed even if @(':print') is @('nil');
       the generated functions are not printed separately
       (other than their appearance in the event expansion),
       even if @(':print') is @(':result') or @(':all');
       no ACL2 output is printed even if @(':print') is @(':all')
       (because the event expansion is not submitted).
       If the call to @('defarbrec') is redundant
       (see the `Redundancy' section below),
       the event expansion generated by the existing call is printed.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Generated Functions")

   (xdoc::desc
    "@('update*-x1'), ..., @('update*-xn')"
    (xdoc::p
     "The iterated argument update functions:")
    (xdoc::codeblock
     "(defun update*-xi (k x1 ... xn)"
     "  (if (zp k)"
     "      xi"
     "    (update*-xi (1- k)"
     "                update-x1<x1,...,xn>"
     "                ..."
     "                update-xn<x1,...,xn>)))"))

   (xdoc::desc
    "@('terminates')"
    (xdoc::p
     "The predicate that tests the termination of the program-mode function:")
    (xdoc::codeblock
     "(defun-sk terminates (x1 ... xn)"
     "  (exists k test<(update*-x1 k x1 ... xn),"
     "                 ..."
     "                 (update*-xn k x1 ... xn)>))"))

   (xdoc::desc
    "@('measure')"
    (xdoc::p
     "The measure function for the logic-mode function:")
    (xdoc::codeblock
     "(defun measure (x1 ... xn k)"
     "  (declare (xargs :measure (nfix (- (terminates-witness x1 ... xn)"
     "                                    (nfix k)))))"
     "  (let ((k (nfix k)))"
     "    (if (or test<(update*-x1 k x1 ... xn),"
     "                 ...,"
     "                 (update*-xn k x1 ... xn)>"
     "            (>= k (nfix (terminates-witness x1 ... xn))))"
     "        k"
     "      (measure x1 ... xn (1+ k)))))"))

   (xdoc::desc
    "@('fn')"
    (xdoc::p
     "The logic-mode function:")
    (xdoc::codeblock
     "(defun fn (x1 ... xn)"
     "  (declare (xargs :measure (measure x1 ... xn 0)"
     "                  :well-founded-relation o<))"
     "  (if (terminates x1 ... xn)"
     "      (if test<x1,...,xn>"
     "          base<x1,...,xn>"
     "        combine<x1,...,xn,(fn update-x1<x1,...,xn>"
     "                              ..."
     "                              update-xn<x1,...,xn>)>)"
     "    nonterminating))"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::h3 "Redundancy")

   (xdoc::p
    "A call of @('defarbrec') is redundant if and only if
     it is identical to a previous successful call of @('defarbrec')
     whose @(':show-only') is not @('t'),
     except that the two calls may differ in
     their @(':print') and @(':show-only') options.
     These options do not affect the generated events,
     and thus they are ignored for the purpose of redundancy.")

   (xdoc::p
    "A call to @('defarbrec') whose @(':show-only') is @('t')
     does not generate any event.
     No successive call may be redundant with such a call.")

   (xdoc::p
    "If a call to @('defarbrec') has the same @('fn')
     as a previous call whose @(':show-only') is not @('t'),
     but the two calls are not identical
     (ignoring the @(':print') and @(':show-only') options),
     the second call causes an error.")))
