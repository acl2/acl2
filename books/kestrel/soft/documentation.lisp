; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft

  :parents (acl2::kestrel-books acl2::macro-libraries acl2::projects)

  :short "SOFT (Second-Order Functions and Theorems)
          is a tool to mimic second-order functions and theorems
          in the first-order logic of ACL2."

  :long

  (xdoc::topstring

   (xdoc::p
    "In SOFT,
     second-order functions are mimicked
     by first-order functions that depend on
     explicitly designated uninterpreted functions
     that mimic function variables.
     First-order theorems over these second-order functions
     mimic second-order theorems universally quantified over function variables.
     Instances of second-order functions and theorems
     are systematically generated
     by replacing function variables with functions.
     Theorem instances are proved automatically,
     via automatically generated
     <see topic='@(url acl2::functional-instantiation)'>functional
     instantiations</see>.")

   (xdoc::p
    "SOFT does not extend the ACL2 logic.
     It is a library that provides macros to introduce
     function variables,
     second-order functions,
     second-order theorems,
     and instances thereof.
     The macros modify the ACL2 state
     only by submitting sound and conservative events;
     they cannot introduce unsoundness or inconsistency on their own.")

   (xdoc::p
    "The
     <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
     >ACL2-2015 Workshop paper on SOFT</a>
     provides
     an overview of the SOFT macros and some simple examples of their use,
     a description of the use of SOFT in program refinement,
     and a discussion of related and future work.
     The presentation of the Workshop talk is available
     <a href=
      \"http://www.cs.utexas.edu/users/moore/acl2/workshop-2015/program.html\"
     >here</a>.
     The examples from the paper are in
     @('[books]/kestrel/soft/workshop-paper-examples.lisp');
     the examples from the talk that are not in the paper are in
     @('[books]/kestrel/soft/workshop-talk-examples.lisp').
     As SOFT is being extended and improved over time,
     some of the contents of the paper and presentation are becoming outdated.
     This manual provides up-to-date information about SOFT.
     The differences between the current version of SOFT
     and the contents of the Workshop paper and presentation
     are described <see topic='@(url updates-to-workshop-material)'>here</see>.
     Also see <see topic='@(url soft-future-work)'>here</see>
     for an up-to-date description of future work."))

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-notions

  :parents (soft)

  :short "Notions that the SOFT macros are based on."

  :long

  (xdoc::topstring-p
   "The macros provided by SOFT are based on the notions
    defined in the sub-topics below.")

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ soft-macros

  :parents (soft)

  :short "Macros provided by SOFT."

  :long

  (xdoc::topstring

   (xdoc::p
    "@(tsee defunvar),
     @(tsee defun2),
     @(tsee defchoose2), and
     @(tsee defun-sk2)
     are wrappers of existing events
     that record function variables and dependencies on them.
     They set the stage for @(tsee defun-inst) and @(tsee defthm-inst).")

   (xdoc::p
    "@(tsee defun-inst) provides the ability to concisely generate functions,
     and automatically prove their termination if recursive,
     by specifying replacements of function variables.")

   (xdoc::p
    "@(tsee defthm-inst) provides the ability to
     concisely generate and automatically prove theorems,
     by specifying replacements of function variables."))

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variables

  :parents (soft-notions)

  :short "Notion of function variable."

  :long

  (xdoc::topstring

   (xdoc::p
    "A function variable is an uninterpreted ACL2 function
     introduced via @(tsee defunvar).
     This macro specifies the arity of the function variable.")

   (xdoc::p
    "A function variable is used in
     <see topic='@(url second-order-functions)'>second-order functions</see> and
     <see topic='@(url second-order-theorems)'>second-order theorems</see>
     as a placeholder for any function with the same arity.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ second-order-functions

  :parents (soft-notions)

  :short "Notion of second-order function."

  :long

  (xdoc::topstring

   (xdoc::p
    "A second-order function is an ACL2 function
     that <see topic='@(url function-variable-dependency)'>depends</see> on
     one or more <see topic='@(url function-variables)'>function variables</see>
     and that is introduced via
     @(tsee defun2), @(tsee defchoose2), or @(tsee defun-sk2).")

   (xdoc::p
    "The function variables that the second-order function depends on
     may be replaced by functions of matching arities,
     obtaining a new function that is an
     <see topic='@(url second-order-function-instances)'>instance</see>
     of the second-order function."))

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorems

  :parents (soft-notions)

  :short "Notion of second-order theorem."

  :long

  (xdoc::topstring

   (xdoc::p
    "A second-order theorem is an ACL2 theorem
     that <see topic='@(url function-variable-dependency)'>depends</see> on
     one or more
     <see topic='@(url function-variables)'>function variables</see>.
     A second-order theorem is introduced via @(tsee defthm);
     SOFT does not provide macros to introduce second-order theorems.")

   (xdoc::p
    "The second-order theorem is universally quantified
     over the function variables that it depends on.
     These function variables may be replaced by functions of matching arities,
     obtaining a new theorem that is an
     <see topic='@(url second-order-theorem-instances)'>instance</see>
     of the second-order theorem.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-function-instances

  :parents (soft-notions)

  :short "Notion of instance of a second-order function."

  :long

  (xdoc::topstring

   (xdoc::p
    "An instance of a second-order function is an ACL2 function
     introduced via @(tsee defun-inst),
     which replaces function variables that the second-order function depends on
     with functions with matching arities.
     This macro specifies the replacement as an
     <see topic='@(url function-variable-instantiation)'>instantiation</see>,
     which is applied to the body, measure (if recursive), and guard
     of the second-order function.")

   (xdoc::p
    "The new function is second-order if it still depends on function variables,
     otherwise it is first-order.
     The new function is recursive iff
     the second-order function that is being instantiated is recursive;
     in this case,
     @(tsee defun-inst) generates a termination proof for the new function
     that uses a <see topic='@(url acl2::functional-instantiation)'>functional
     instance</see> of the
     <see topic='@(url termination-theorem)'>termination theorem</see>
     of the second-order function that is being instantiated.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorem-instances

  :parents (soft-notions)

  :short "Notion of instance of a second-order theorem."

  :long

  (xdoc::topstring

   (xdoc::p
    "An instance of a second-order theorem is an ACL2 theorem
     introduced via @(tsee defthm-inst),
     which replaces function variables that the second-order theorem depends on
     with functions of matching arities.
     This macro specifies the replacement as an
     <see topic='@(url function-variable-instantiation)'>instantiation</see>,
     which is applied to the formula of the second-order theorem.")

   (xdoc::p
    "The new theorem is second-order if it still depends on function variables,
     otherwise it is first-order.
     @(tsee defthm-inst) generates a proof for the new theorem
     that uses a <see topic='@(url acl2::functional-instantiation)'>functional
     instance</see> of the second-order theorem that is being instantiated.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-dependency

  :parents (soft-notions)

  :short "Notion of dependency on function variables."

  :long

  (xdoc::topstring

   (xdoc::p
    "A <see topic='@(url acl2::term)'>term</see> @('term') depends on
     a <see topic='@(url function-variables)'>function variable</see> @('fvar')
     iff @('fvar') occurs in @('term')
     or @('fvar') is one of the function variables that
     a <see topic='@(url second-order-functions)'>second-order
     function</see> that occurs in @('term') depends on..")

   (xdoc::p
    "A <see topic='@(url second-order-functions)'>second-order function</see>
     @('sofun') depends on a function variable @('fvar')
     iff its body, guard, or (if present) measure depends on @('fvar').")

   (xdoc::p
    "A <see topic='@(url second-order-theorems)'>second-order theorem</see>
     @('sothm') depends on a function variable @('fvar')
     iff its formula depends on @('fvar').")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::p
    "Given")
   (xdoc::codeblock
    "(defunvar ?f (*) => *)"
    "(defunvar ?g (*) => *)"
    "(defun2 h[?f] (x) (?f (cons x 3)))")
   (xdoc::p
    "the term @('(h[?f] (?g a))') depends exactly on @('?g') and @('?f').")

   (xdoc::h4 "Example 2")

   (xdoc::p
    "Given")
   (xdoc::codeblock
    "(defunvar ?f (*) => *)"
    "(defunvar ?g (*) => *)"
    "(defun2 h[?f] (x) (?f (cons x 3)))"
    "(defun2 k[?f][?g] (a) (h[?f] (?g a)))")
   (xdoc::p
    "the function @('k[?f][?g]') depends exactly on @('?g') and @('?f').")

   (xdoc::h4 "Example 3")

   (xdoc::p
    "Given")
   (xdoc::codeblock
    "(defunvar ?f (*) => *)"
    "(defunvar ?g (*) => *)"
    "(defun2 h[?f] (x) (?f (cons x 3)))"
    "(defthm th (h[?f] (?g a)))")
   (xdoc::p
    "the theorem @('th') depends exactly on @('?g') and @('?f').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-instantiation

  :parents (soft-notions)

  :short "Notion of function variable instantiation."

  :long

  (xdoc::topstring

   (xdoc::p
    "A function variable instantiation is
     an <see topic='@(url acl2::alists)'>alist</see>")
   (xdoc::codeblock
    "((fvar1 . fun1) ... (fvarN . funN))")
   (xdoc::p
    "where @('N') is a non-negative integer,
     @('fvar1'), ..., @('fvarN') are distinct
     <see topic='@(url function-variables)'>function variables</see>,
     and @('fun1'), ..., @('funN') are named functions
     such that each @('funI') has the same arity as
     the corresponding @('fvarI').
     The @('funI') functions may be
     <see topic='@(url function-variables)'>function variables</see>,
     <see topic='@(url second-order-functions)'>second-order functions</see>,
     or ``regular'' first-order functions.")

   (xdoc::p
    "An instantiation as above is applied
     to a <see topic='@(url acl2::term)'>term</see> @('term')
     by replacing each @('fvarI') with @('funI').
     This involves not only explicit occurrences of @('fvarI'),
     but also implicit occurrences as function variables upon which
     second-order functions occurring in @('term') depend on.
     For the latter kind of occurrences,
     suitable
     <see topic='@(url second-order-function-instances)'>instances</see>
     of such second-order functions must exist;
     if they do not exist, the application of the instantiation fails.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::p
    "Given")
   (xdoc::codeblock
    "(defunvar ?f (*) => *)"
    "(defunvar ?g (*) => *)"
    "(defun2 h[?f] (x) ...)"
    "(defun2 k[?f] (x) ...)"
    "(defun-inst h[consp] (h[?f] (?f . consp)))")
   (xdoc::p
    "the alist @('((?f . consp) (?g . k[?f]))') is an instantiation,
     and the result of applying it to the term @('(h[?f] (?g a))')
     is the term @('(h[consp] (k[?f] a))').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defunvar

  :parents (soft-macros function-variables)

  :short "Introduce function variable."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defunvar fvar (* ... *) => *"
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('fvar')"
    (xdoc::p
     "A symbol, which names the
      <see topic='@(url function-variables)'>function variable</see>.
      It must be a valid function name that is not already in use."))

   (xdoc::desc
    "@('(* ... *)')"
    (xdoc::p
     "A list of zero or more @('*') signs,
      which defines the arity of @('fvar')."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') (the default) to print only any error output."))

   (xdoc::h3 "Generated Events")

   (xdoc::codeblock
    "(defstub fvar (* ... *) => *)")

   (xdoc::p
    "@('fvar') is introduced as
     an uninterpreted function with the given arity.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; A unary function variable:"
    "(defunvar ?f (*) => *)")

   (xdoc::h4 "Example 2")

   (xdoc::codeblock
    ";; A unary function variable:"
    "(defunvar ?p (*) => *)")

   (xdoc::h4 "Example 3")

   (xdoc::codeblock
    ";; A binary function variable:"
    "(defunvar ?g (* *) => *)")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "Starting function variable names with @('?') (as in the examples above)
     provides a visual cue for their function variable status.
     However, SOFT does not enforce this naming convention.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defun)."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defun2 sofun (var1 ... varM)"
    "  doc-string"
    "  declaration ... declaration"
    "  body"
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('sofun')"
    (xdoc::p
     "A symbol, which names the
      <see topic='@(url second-order-functions)'>second-order function</see>.
      It must be a valid function name that is not already in use."))

   (xdoc::desc
    "@('(var1 ... varM)')"
    (xdoc::p
     "A list of parameters, as in @(tsee defun)."))

   (xdoc::desc
    "@('doc-string')"
    (xdoc::p
     "An optional documentation string, as in @(tsee defun)."))

   (xdoc::desc
    "@('declaration ... declaration')"
    (xdoc::p
     "Zero or more declarations, as in @(tsee defun)."))

   (xdoc::desc
    "@('body')"
    (xdoc::p
     "A defining body, as in @(tsee defun).
      If @('sofun') is recursive,
      its well-founded relation must be @(tsee o<)."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') to print only any error output;
      @(':fn-output') (the default) to print only
      the (possibly error) output from the generated @(tsee defun).
      In all cases, the function variables that the function depends on
      are printed."))

   (xdoc::h3 "Generated Events")

   (xdoc::codeblock
    "(defun sofun (var1 ... varM)"
    "  doc-string"
    "  declaration ... declaration"
    "  body)")

   (xdoc::p
    "@('sofun') is introduced as a first-order function using @(tsee defun).
     The function variables that @('sofun') depends on are also recorded.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; A non-recursive function that applies four times"
    ";; its function parameter to its individual parameter:"
    "(defun2 quad[?f] (x)"
    "  (?f (?f (?f (?f x)))))")

   (xdoc::h4 "Example 2")

   (xdoc::codeblock
    ";; A recursive predicate that recognizes true lists"
    ";; whose elements satisfy the predicate parameter:"
    "(defun2 all[?p] (l)"
    "  (cond ((atom l) (null l))"
    "        (t (and (?p (car l)) (all[?p] (cdr l))))))")

   (xdoc::h4 "Example 3")

   (xdoc::codeblock
    ";; A recursive function that homomorphically lifts ?F"
    ";; to operate on true lists whose elements satisfy ?P:"
    "(defun2 map[?f][?p] (l)"
    "  (declare (xargs :guard (all[?p] l)))"
    "  (cond ((endp l) nil)"
    "        (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))"
    ";; The predicate parameter ?P only occurs in the guard, not in the body.")

   (xdoc::h4 "Example 4")

   (xdoc::codeblock
    ";; A generic folding function on values as binary trees:"
    "(defun2 fold[?f][?g] (bt)"
    "  (cond ((atom bt) (?f bt))"
    "        (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "Ending second-order function names
     with the function variables it depends on (in any order),
     enclosed in square brackets
     (as in the examples above)
     conveys the dependency on the function variables
     and provides a visual cue for their implicit presence.
     However, SOFT does not enforce this naming convention.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defchoose2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defchoose)."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defchoose2 sofun (bvar1 ... bvarP) (var1 ... varM)"
    "  body"
    "  :strengthen ..."
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('sofun')"
    (xdoc::p
     "A symbol, which names the
      <see topic='@(url second-order-functions)'>second-order function</see>.
      It must be a valid function name that is not already in use."))

   (xdoc::desc
    "@('(bvar1 ... bvarP)')"
    (xdoc::p
     "A list of bound variables (or a single variable),
      as in @(tsee defchoose)."))

   (xdoc::desc
    "@('(var1 ... varM)')"
    (xdoc::p
     "A list of parameters, as in @(tsee defchoose)."))

   (xdoc::desc
    "@('body')"
    (xdoc::p
     "A defining body, as in @(tsee defchoose)."))

   (xdoc::desc
    "@(':strengthen ...')"
    (xdoc::p
     "An option to strengthen the axiom, as in @(tsee defchoose)."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') to print only any error output;
      @(':fn-output') (the default) to print only
      the (possibly error) output from the generated @(tsee defchoose).
      In all cases, the function variables that the function depends on
      are printed."))

   (xdoc::h3 "Generated Events")

   (xdoc::codeblock
    "(defchoose2 sofun (bvar1 ... bvarP) (var1 ... varM)"
    "  body"
    "  :strengthen ...)")

   (xdoc::p
    "@('sofun') is introduced as a first-order function using @(tsee defchoose).
     The function variables that @('sofun') depends on are also recorded.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; A function constrained to return a fixed point of ?F, if any exists:"
    "(defchoose2 fixpoint[?f] x ()"
    "  (equal (?f x) x))")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "The same naming convention for the functions introduced by @(tsee defun2)
     apply to the functions introduced by @(tsee defchoose2).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-sk2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defun-sk)."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defun-sk sofun (var1 ... varM)"
    "  body"
    "  :rewrite ..."
    "  :quant-ok ..."
    "  :skolem-name ..."
    "  :thm-name ..."
    "  :witness-dcls ..."
    "  :strengthen ..."
    "  :constrain ..."
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('sofun')"
    (xdoc::p
     "A symbol, which names the
      <see topic='@(url second-order-functions)'>second-order function</see>.
      It must be a valid function name that is not already in use."))

   (xdoc::desc
    "@('(var1 ... varM)')"
    (xdoc::p
     "A list of parameters, as in @(tsee defun-sk)."))

   (xdoc::desc
    "@('body')"
    (xdoc::p
     "A defining body, as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':rewrite ...')"
    (xdoc::p
     "An option to customize the rewrite rule, as in @(tsee defun-sk).
      If a term is supplied,
      it must <see topic='@(url function-variable-dependency)'>depend</see> on
      the same function variables that @('body')
      <see topic='@(url function-variable-dependency)'>depends</see> on.
      As in @(tsee defun-sk), this option may be present
      only if the quantifier is universal."))

   (xdoc::desc
    "@(':quant-ok ...')"
    (xdoc::p
     "An option to allow @(tsee acl2::forall) and @(tsee acl2::exists)
      in the matrix of @('body'),
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':skolem-name ...')"
    (xdoc::p
     "An option to customize the name of the witness function,
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':thm-name ...')"
    (xdoc::p
     "An option to customize the name of the rewrite rule,
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':witness-dcls ...')"
    (xdoc::p
     "An option to customize the declarations of @('sofun'),
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':strengthen ...')"
    (xdoc::p
     "An option to strengthen the axiom introduced by @(tsee defchoose),
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':constrain')"
    (xdoc::p
     "An option for constraining, instead of defining, the function,
      as in @(tsee defun-sk)."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') to print only any error output;
      @(':fn-output') (the default) to print only
      the (possibly error) output from the generated @(tsee defun-sk).
      In all cases, the function variables that the function depends on
      are printed."))

   (xdoc::h3 "Generated Events")

   (xdoc::codeblock
    "(defun-sk sofun (var1 ... varM)"
    "  body"
    "  :rewrite ..."
    "  :quant-ok ..."
    "  :skolem-name ..."
    "  :thm-name ..."
    "  :witness-dcls ..."
    "  :strengthen ...)")

   (xdoc::p
    "@('sofun') is introduced as a first-order function using @(tsee defun-sk).
     The function variables that @('sofun') depends on are also recorded.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; A predicate that recognizes injective functions:"
    "(defun-sk2 injective[?f] ()"
    " (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "The same naming convention for the functions introduced by @(tsee defun2)
     apply to the functions introduced by @(tsee defun-sk2).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-inst

  :parents (soft-macros second-order-function-instances)

  :short "Introduce function by instantiating a second-order functions."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defun-inst fun"
    "  (sofun (fvar1 . fun1) ... (fvarN . funN))"
    "  :verify-guards ..."
    "  :skolem-name ..."
    "  :thm-name ..."
    "  :rewrite ..."
    "  :constrain ..."
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('fun')"
    (xdoc::p
     "A symbol, which names the new function obtained by
      <see topic='@(url second-order-function-instances)'>instantiating</see>
      @('sofun').
      It must be a valid function name that is not already in use."))

   (xdoc::desc
    "@('sofun')"
    (xdoc::p
     "Name of the second-order function to instantiate."))

   (xdoc::desc
    "@('((fvar1 . fun1) ... (fvarN . funN))')"
    (xdoc::p
     "An
      <see topic='@(url function-variable-instantiation)'>instantiation</see>,
      which specifies how to generate @('fun') from @('sofun').
      The function variables @('fvar1'), ..., @('fvarN')
      must be function parameters of @('sofun')."))

   (xdoc::desc
    "@(':verify-guards')"
    (xdoc::p
     "An option to attempt or omit the guard verification of @('fun').
      This may be present only if @('sofun') was introduced via @(tsee defun2).
      If this flag is absent,
      the guard verification of @('fun') is attempted
      iff @('sofun') is guard-verified.")
    (xdoc::p
     "In general it is not possible to verify the guards
      of an instance of a second-order function
      from the <see topic='@(url guard-theorem)'>guard theorem</see>
      of the second-order function,
      because function variables have guard @('t')
      but may be replaced with functions with stricter guards.
      Since @(tsee defun-inst) currently does not provide
      an option to supply guard verification hints for @('fun'),
      @(':verify-guards nil') may be used to defer
      the guard verification of @('fun')
      when it is not accomplished automatically (i.e. without hints).
      (An option to supply guard verification hints
      will be added to @(tsee defun-inst).)"))

   (xdoc::desc
    "@(':skolem-name')"
    (xdoc::p
     "An option to customize the name of the witness function of @('fun').
      This may be present
      only if @('sofun') was introduced via @(tsee defun-sk2).
      If present,
      it is passed to the @(tsee defun-sk) generated for @('fun')."))

   (xdoc::desc
    "@(':thm-name')"
    (xdoc::p
     "An option to customize the name of the rewrite rule of @('fun').
      This may be present
      only if @('sofun') was introduced via @(tsee defun-sk2).
      If present,
      it is passed to the @(tsee defun-sk) generated for @('fun')."))

   (xdoc::desc
    "@(':rewrite')"
    (xdoc::p
     "An option to customize the rewrite rule of @('fun').
      This may be present only if
      @('sofun') was introduced via @(tsee defun-sk2)
      and its quantifier is universal.
      If present, it is passed to the @(tsee defun-sk) generated for @('fun').
      If a term is supplied,
      it must <see topic='@(url function-variable-dependency)'>depend</see> on
      the same function variables that the body of @('fun')
      <see topic='@(url function-variable-dependency)'>depends</see> on;
      in particular, if @('fun') is first-order,
      the term supplied as rewrite rule
      must not depend on any function variables.
      If this option is absent,
      @('sofun') was introduced via @(tsee defun-sk2),
      and its quantifier is universal,
      then the rewrite rule of @('fun') has the same form as in @('sofun');
      in particular, the function variables in the rewrite rule of @('sofun')
      are instantiated via the instantiation passed to @(tsee defun-inst)."))

   (xdoc::desc
    "@(':constrain')"
    (xdoc::p
     "An option for constraining, instead of defining, @('fun').
      This may be present only if
      @('sofun') was introduced via @(tsee defun-sk2).
      If present, it is passed to the @(tsee defun-sk) generated for @('fun').
      If this options is absent,
      then @('fun') is constrained if @('sofun') is constrained,
      and @('fun') is defined if @('sofun') is defined."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') to print only any error output;
      @(':result') (the default) to print only
      the generated function form and any error output.
      In all cases, the function variables that the new function depends on
      are printed;
      if the new function is first-order,
      its dependence on no function variables is also printed."))

   (xdoc::h3 "Generated Events")

   (xdoc::p
    "One of the following:")

   (xdoc::ul

    (xdoc::li
     (xdoc::codeblock
      "(defun2 fun ...)")
     (xdoc::p
      "if @('sofun') was introduced via @(tsee defun2).
       The body, measure (if recursive), and guard of @('fun')
       are obtained by
       <see topic='@(url function-variable-instantiation)'>applying
       the instantiation</see>
       to the body, measure (if recursive), and guard of @('sofun').
       If @('fun') is recursive,
       its termination proof uses
       a <see topic='@(url acl2::functional-instantiation)'>functional
       instance</see> of the
       <see topic='@(url termination-theorem)'>termination theorem</see>
       of @('sofun')."))

    (xdoc::li
     (xdoc::codeblock
      "(defchoose2 fun (bvar1 ... bvarP) ...)")
     (xdoc::p
      "if @('sofun') was introduced via @(tsee defchoose2).
       The body of @('fun')
       is obtained by
       <see topic='@(url function-variable-instantiation)'>applying
       the instantiation</see>
       to the body of @('sofun').
       The @(':strengthen') value of @('fun') is the same as @('sofun')."))

    (xdoc::li
     (xdoc::codeblock
      "(defun-sk2 fun ...)")
     (xdoc::p
      "if @('sofun') was introduced via @(tsee defun-sk2).
       The body and guard of @('fun')
       are obtained by
       <see topic='@(url function-variable-instantiation)'>applying
       the instantiation</see>
       to the body and guard of @('sofun').
       The guard of @('fun') is not verified.
       The @(':strengthen') value of @('fun') is the same as @('sofun').
       The @(':quant-ok') value of @('fun') is @('t').")))

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; Apply ?F four times to X:"
    "(defun2 quad[?f] (x)"
    "  (?f (?f (?f (?f x)))))"
    ""
    ";; Wrap a value into a singleton list:"
    "(defun wrap (x) (list x))"
    ""
    ";; Wrap a value four times:"
    "(defun-inst quad[wrap]"
    "  (quad[?f] (?f . wrap)))")

   (xdoc::h4 "Example 2")

   (xdoc::codeblock
    ";; Recognize true lists of values that satisfy ?P:"
    "(defun2 all[?p] (l)"
    "  (cond ((atom l) (null l))"
    "        (t (and (?p (car l)) (all[?p] (cdr l))))))"
    ""
    ";; Recognize octets:"
    "(defun octetp (x) (and (natp x) (< x 256)))"
    ""
    ";; Recognize true lists of octets:"
    "(defun-inst all[octetp]"
    "  (all[?p] (?p . octetp)))")

   (xdoc::h4 "Example 3")

   (xdoc::codeblock
    ";; Homomorphically lift ?F to on true lists of ?P values:"
    "(defun2 map[?f][?p] (l)"
    "  (declare (xargs :guard (all[?p] l)))"
    "  (cond ((endp l) nil)"
    "        (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))"
    ""
    ";; Translate lists of octets to lists of characters:"
    "(defun-inst map[code-char][octetp]"
    "  (map[?f][?p] (?f . code-char) (?p . octetp)))"
    ";; The replacement CODE-CHAR of ?F"
    ";; induces the replacement OCTETP of ?P,"
    ";; because the guard of CODE-CHAR is (equivalent to) OCTECTP."
    ";; The creation of the MAP[CODE-CHAR][OCTETP] instance of MAP[?F][?P]"
    ";; needs the instance ALL[OCTETP) of ALL[?P] (in the guard),"
    ";; created as in the earlier example.")

   (xdoc::h4 "Example 4")

   (xdoc::codeblock
    ";; Folding function on binary trees:"
    "(defun2 fold[?f][?g] (bt)"
    "  (cond ((atom bt) (?f bt))"
    "        (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))"
    ""
    ";; Add up all the natural numbers in a tree, coercing other values to 0:"
    "(defun-inst fold[nfix][binary-+]"
    "  (fold[?f][?g] (?f . nfix) (?g . binary-+)))")

   (xdoc::h4 "Example 5")

   (xdoc::codeblock
    ";; Return a fixed point of ?F, if any exists:"
    "(defchoose2 fixpoint[?f] x ()"
    "  (equal (?f x) x))"
    ""
    ";; Double a value:"
    "(defun twice (x) (* 2 (fix x)))"
    ""
    ";; Function constrained to return the (only) fixed point 0 of TWICE:"
    "(defun-inst fixpoint[twice]"
    "  (fixpoint[?f] (?f . twice)))")

   (xdoc::h4 "Example 6")

   (xdoc::codeblock
    ";; Recognize injective functions:"
    "(defun-sk2 injective[?f] ()"
    "  (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))"
    ""
    ";; Recognize functions whose four-fold application is injective:"
    "(defun-inst injective[quad[?f]] (?f)"
    "  (injective[?f] (?f . quad[?f])))")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "If the name of the second-order function that is being instantiated
     follows the naming convention described for
     @(tsee defun2), @(tsee defchoose2), and @(tsee defun-sk2),
     the name of the instance can be obtained
     by replacing the names of the function variables between square brackets
     with the names of the replacing functions in the instantiation
     (as in the examples above).
     This conveys the idea of applying the second-order function
     to the functions that replace the function variables.
     However, SOFT does not enforce this naming convention.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defthm-2nd-order

  :parents (soft-macros second-order-theorems)

  :short "Introduce second-order theorem."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defthm sothm"
    "  formula"
    "  :rule-classes ..."
    "  :instructions ..."
    "  :hints ..."
    "  :otf-flg ...)")

   (xdoc::p
    "This is a normal @(tsee defthm).
     SOFT does not provide macros for introducing second-order theorems,
     at this time.")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('sothm')"
    (xdoc::p
     "Name of the
     <see topic='@(url second-order-theorems)'>second-order theorem</see>,
     as in @(tsee defthm)."))

   (xdoc::desc
    "@('formula')"
    (xdoc::p
     "Formula of the theorem, as in @(tsee defthm).
     If @('formula')
     <see topic='@(url function-variable-dependency)'>depends</see>
     on some <see topic='@(url function-variables)'>function variables</see>,
     @('sothm') is a second-order theorem."))

   (xdoc::desc
    "@(':rule-classes')"
    (xdoc::p
     "Rule classes of the theorem, as in @(tsee defthm)."))

   (xdoc::desc
    "@(':instructions')"
    (xdoc::p
     "Proof checker instructions to prove the theorem, as in @(tsee defthm)."))

   (xdoc::desc
    "@(':hints')"
    (xdoc::p
     "Hints to prove the theorem, as in @(tsee defthm)."))

   (xdoc::desc
    "@(':otf-flg')"
    (xdoc::p
     "`Onward Thru the Fog' flag, as in @(tsee defthm)."))

   (xdoc::h3 "Generated Events")

   (xdoc::p
    "The @(tsee defthm) itself.")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; Homomorphically lift ?F to on true lists of ?P values:"
    "(defun2 map[?f][?p] (l)"
    "  (declare (xargs :guard (all[?p] l)))"
    "  (cond ((endp l) nil)"
    "        (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))"
    ""
    ";; The homomorphic lifting of ?F to lists of ?P values"
    ";; preserves the length of the list,"
    ";; for every function ?F and predicate ?P:"
    "(defthm len-of-map[?f][?p]"
    "  (equal (len (map[?f][?p] l)) (len l)))")

   (xdoc::h4 "Example 2")

   (xdoc::codeblock
    ";; Recognize injective functions:"
    "(defun-sk2 injective[?f] ()"
    "  (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))"
    ""
    ";; The four-fold application of an injective function is injective:"
    "(defthm injective[quad[?f]]-when-injective[?f]"
    "  (implies (injective[?f]) (injective[quad[?f]]))"
    "  :hints ...)")

   (xdoc::h4 "Example 3")

   (xdoc::codeblock
    ";; Folding function on binary trees:"
    "(defun2 fold[?f][?g] (bt)"
    "  (cond ((atom bt) (?f bt))"
    "        (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))"
    ""
    ";; Abstract input/output relation:"
    "(defunvar ?io (* *) => *)"
    ""
    ";; Recognize functions ?F that satisfy the input/output relation on atoms:"
    "(defun-sk2 atom-io[?f][?io] ()"
    "  (forall x (implies (atom x) (?io x (?f x))))"
    "  :rewrite :direct)"
    ""
    ";; Recognize functions ?G that satisfy"
    ";; the input/output relation on CONSP pairs"
    ";; when the arguments are valid outputs for the CAR and CDR components:"
    "(defun-sk2 consp-io[?g][?io] ()"
    "  (forall (x y1 y2)"
    "          (implies (and (consp x) (?io (car x) y1) (?io (cdr x) y2))"
    "                   (?io x (?g y1 y2))))"
    "  :rewrite :direct)"
    ""
    ";; The generic folding function on binary trees"
    ";; satisfies the input/output relation"
    ";; when its function parameters satisfy the predicates just introduced:"
    "(defthm fold-io[?f][?g][?io]"
    "  (implies (and (atom-io[?f][?io]) (consp-io[?g][?io]))"
    "           (?io x (fold[?f][?g] x))))")

   (xdoc::h3 "Naming Conventions")

   (xdoc::p
    "Including in the name of a second-order theorem,
     between square brackets (in any order),
     the function variables that the theorem depends on,
     makes the dependency more explicit when referencing the theorem.
     This naming convention may arise naturally
     when the name of the theorem includes names of second-order functions
     that follow the analogous naming convention
     (as in the @('len-of-map[?f][?p]') example above),
     or it may be explicitly followed when choosing the name of the theorem
     (as in the @('fold-io[?f][?g][?io]') example above).
     However, SOFT does not enforce this naming convention.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defthm-inst

  :parents (soft-macros second-order-theorem-instances)

  :short "Introduce theorem by instantiating a second-order theorem."

  :long

  (xdoc::topstring

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defthm-inst thm"
    "  (sothm (fvar1 . fun1) ... (fvarN . funN))"
    "  :rule-classes ..."
    "  :print ...)")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('thm')"
    (xdoc::p
     "A symbol, which names the new theorem obtained by
     <see topic='@(url second-order-theorem-instances)'>instantiating</see>
     @('sothm').
     It must be a valid theorem name that is not already in use."))

   (xdoc::desc
    "@('sothm')"
    (xdoc::p
     "Name of the second-order theorem to instantiate."))

   (xdoc::desc
    "@('((fvar1 . fun1) ... (fvarN . funN))')"
    (xdoc::p
     "An
      <see topic='@(url function-variable-instantiation)'>instantiation</see>,
      which specifies how to generate @('thm') from @('sothm').
      @('sothm') must
      <see topic='@(url function-variable-dependency)'>depend</see>
      on at least the function variables @('fvar1'), ..., @('fvarN')."))

   (xdoc::desc
    "@(':rule-classes')"
    (xdoc::p
     "An option to specify the rule classes of @('thm')."))

   (xdoc::desc
    "@(':print ...')"
    (xdoc::p
     "An option to customize the screen output:
      @(':all') to print all the output;
      @('nil') to print only any error output;
      @(':result') (the default) to print only
      the generated theorem form and any error output."))

   (xdoc::h3 "Generated Events")

   (xdoc::codeblock
    "(defthm thm"
    "  formula"
    "  ... ; proof"
    "  :rule-classes ...)")

   (xdoc::p
    "@('thm') is introduced as a theorem,
     whose formula @('formula') is obtained by
     <see topic='@(url function-variable-instantiation)'>applying
     the instantiation</see> to the formula of @('sothm').
     The proof uses
     a <see topic='@(url acl2::functional-instantiation)'>functional
     instance</see> of @('sothm').
     If @(':rule-classes') is supplied to @(tsee defthm-inst),
     its value is used for @('thm');
     otherwise, its value is copied from @('sothm').")

   (xdoc::h3 "Examples")

   (xdoc::h4 "Example 1")

   (xdoc::codeblock
    ";; Homomorphically lift ?F to on true lists of ?P values:"
    "(defun2 map[?f][?p] (l)"
    "  (declare (xargs :guard (all[?p] l)))"
    "  (cond ((endp l) nil)"
    "        (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))"
    ""
    ";; Translate lists of octets to lists of characters:"
    "(defun-inst map[code-char][octetp]"
    "  (map[?f][?p] (?f . code-char) (?p . octetp)))"
    ""
    ";; The homomorphic lifting of ?F to lists of ?P values"
    ";; preserves the length of the list:"
    "(defthm len-of-map[?f][?p]"
    "  (equal (len (map[?f][?p] l)) (len l)))"
    ""
    ";; MAP[CODE-CHAR][OCTETP] preserves the length of the list:"
    "(defthm-inst len-of-map[code-char][octetp]"
    "  (len-of-map[?f][?p] (?f . code-char) (?p . octetp)))")

   (xdoc::h4 "Example 2")

   (xdoc::codeblock
    ";; Apply ?F four times to X:"
    "(defun2 quad[?f] (x)"
    "  (?f (?f (?f (?f x)))))"
    ""
    ";; Recognize injective functions:"
    "(defun-sk2 injective[?f] ()"
    "  (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))"
    ""
    ";; Recognize functions whose four-fold application is injective:"
    "(defun-inst injective[quad[?f]] (?f)"
    "  (injective[?f] (?f . quad[?f])))"
    ""
    ";; Wrap a value into a singleton list:"
    "(defun wrap (x) (list x))"
    ""
    ";; The four-fold application of an injective function is injective:"
    "(defthm injective[quad[?f]]-when-injective[?f]"
    "  (implies (injective[?f]) (injective[quad[?f]]))"
    "  :hints ...)"
    ""
    ";; Needed by DEFTHM-INST below to apply its instantiation:"
    "(defun-inst injective[quad[wrap]]"
    "  (injective[quad[?f]] (?f . wrap)))"
    ""
    ";; Needed by DEFTHM-INST below to apply its instantiation:"
    "(defun-inst injective[wrap]"
    "  (injective[?f] (?f . wrap)))"
    ""
    ";; QUAD[WRAP] is injective if WRAP is:"
    "(defthm-inst injective[quad[wrap]]-when-injective[wrap]"
    "  (injective[quad[?f]]-when-injective[?f] (?f . wrap)))")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc updates-to-workshop-material

  :parents (soft)

  :short "Updates to SOFT since the ACL2-2015 Workshop."

  :long

  (xdoc::topstring

   (xdoc::h4 "Nullary Function Variables")

   (xdoc::p
    "Nullary function variables (i.e. function variables with arity 0)
     are now allowed.")

   (xdoc::h4 "Naming Conventions")

   (xdoc::p
    "For second-order functions and theorems
     that depend on two or more function variables,
     the Workshop paper suggests to use underscores
     to separate the function variables inside the square brackets,
     e.g. @('sofun[?f_?g_?h]').
     This manual instead suggests
     to enclose each function variable in square brackets,
     e.g. @('sofun[?f][?g][?h]').")

   (xdoc::h4 "Implicit Function Parameters")

   (xdoc::p
    "The @(tsee defun2),
     @(tsee defchoose2),
     @(tsee defun-sk2),
     and @(tsee defun-inst)
     macros no longer include an explicit list of function parameters.
     The function is implicitly parameterized over
     the function variables that it depends on.
     This simplifies the implementation.
     It also avoids the repetition of the function variables
     when using the naming convention of including,
     in the name of a second-order function,
     the function variables that it depends on
     (enclosed in square brackets).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft-future-work

  :parents (soft)

  :short "Some possible improvements and extensions to SOFT."

  :long

  (xdoc::topstring

   (xdoc::h4 "Mutual Recursion")

   (xdoc::p
    "SOFT should be extended with the ability to introduce and instantiate
     mutually recursive functions,
     perhaps via a new @('mutual-recursion2') macro.")

   (xdoc::h4 "Other Well-Founded Relations")

   (xdoc::p
    "Currently recursive second-order functions
     must use @(tsee o<) as their well-founded relation.
     This could be relaxed, perhaps even to the point of
     allowing second-order well-founded relations.")

   (xdoc::h4 "Other Function and Theorem Introduction Macros")

   (xdoc::p
    "Besides second-order versions of
     @(tsee defun), @(tsee defchoose), and @(tsee defun-sk),
     we could add support for second-order versions of
     @(tsee defund), @(tsee defun-nx), @(tsee define), @(tsee defpun),
     and other function introduction events.
     @(tsee defun-inst) would generate the same macros for instances.
     The macros could be called @('defund2'), @('defun-nx2'), etc.")

   (xdoc::p
    "Under some conditions, it would make sense for @(tsee defun-inst)
     to instantiate a partial second-order function
     (introduced, say, via a future @('defpun2') macro)
     to a total second-order function (i.e. a @(tsee defun2) or @(tsee defun)),
     when the instantiated @(':domain') or @(':gdomain') restrictions
     are theorems.")

   (xdoc::p
    "@(tsee defthm-inst) could also generate instances with the same macros
     from second-order theorems introduced via
     @(tsee defthm), @(tsee defrule), and other theorem introduction events.")

   (xdoc::h4 "Program Mode")

   (xdoc::p
    "Currently SOFT only supports logic-mode second-order funcions.
     Supporting program-mode functions as well may be useful.")

   (xdoc::h4 "Guards of Instances of Second-Order Functions")

   (xdoc::p
    "It would be useful to allow
     the default guards of instances of second-order functions
     (obtained by instantiating the guards of the second-order functions)
     to be overridden by stronger guards.")

   (xdoc::p
    "The <see topic='@(url acl2::guard-theorem)'>guard theorem</see>
     of a second-order function may be useful
     (although not sufficient in general)
     to verifies the guards of instances of the second-order function.
     A mechanism to enable the use of that theorem would be useful.")

   (xdoc::p
    "See the future work section of the
     <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
     >Workshop paper</a>
     for a more detailed discussion with examples.")

   (xdoc::h4 "Lambda Expressions")

   (xdoc::p
    "Instantiations could be extended to allow function variables
     to be replaces with lambda expressions, besides named functions.")

   (xdoc::h4 "Transitivity of Instantiations")

   (xdoc::p
    "Intuitively,
     if @('f') is an instance of @('g')
     and @('g') is an instance of @('h'),
     then @('f') should be an instance of @('h').
     This is currently not supported by @(tsee defun-inst),
     but probably it should be.")

   (xdoc::p
    "See the future work section of the
     <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
     >Workshop paper</a>
     for a more detailed discussion with examples.")

   (xdoc::h4 "More Constraints on Function Variables")

   (xdoc::p
    "The types of function variables are currently limited to
     <see topic='@(url acl2::signature)'>signatures</see>
     with single-value results and with no stobjs.
     This could be extended to allow multiple-value results and stobjs.
     Instantiations will have to respect these additional type structures.")

   (xdoc::p
    "Other than their types, function variables are currently unconstrained.
     In some cases, it may be useful to specify some logical constraints,
     resulting in a constrained function as in non-trivial @(tsee encapsulate)s.
     Instantiations will have to respect these additional constraints.")

   (xdoc::p
    "The latter extension would overlap with some existing tools,
     such as @('instance-of-defspec') and @('make-generic-theory').
     Ideally, the functionality of SOFT and those tools would be integrated.")

   (xdoc::p
    "Function variables current have guard @('t').
     It may be useful to allow guards to be specified for function variables.
     Instantiations will have to match these guards.")

   (xdoc::h4 "Automatic Instances")

   (xdoc::p
    "Currently, when an instantiation is applied to a term,
     the table of instances of second-order functions is consulted
     to find replacements for certain second-order functions,
     and the application of the instantiation fails
     if replacements are not found.
     Thus, all the needed instances must be introduced
     before applying the instantiation.
     SOFT could be extended to generate automatically
     the needed instances of second-order functions.")

   (xdoc::p
    "SOFT could also be extended with a macro @('defthm2')
     to prove a second-order theorem via @(tsee defthm)
     and to record the theorem in a new table,
     along with information about the involved second-order functions.
     @(tsee defun-inst) could be extended with
     the option to generate instances of the second-order theorems
     that involve the second-order function being instantiated.
     @('defthm2') could include the option to generate
     instances of the theorem that correspond
     to the known instances of the second-order functions
     that the theorem involves.
     These extensions would reduce the use of explicit @(tsee defthm-inst)s.")

   (xdoc::p
    "The convention of including function variables in square brackets
     in the names of second-order functions and theorems,
     could be exploited to name the automatically generated
     function and theorem instances.")

   (xdoc::h4 "Default Rule Classes")

   (xdoc::p
    "Currently the default rule classes
     of an instance of a second-order theorem are @('(:rewrite)'),
     but perhaps the default should be the rule classes
     of the second-order theorem that is being instantiated.")))
