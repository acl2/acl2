; SOFT ('Second-Order Functions and Theorems')
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides SOFT ('Second-Order Functions and Theorems'),
; a tool to mimic second-order functions and theorems
; in the first-order logic of ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft

  :parents (acl2::kestrel-books acl2::macro-libraries)

  :short
  "SOFT (&lsquo;Second-Order Functions and Theorems&rsquo;),
  a tool to mimic second-order functions and theorems
  in the first-order logic of ACL2."

  :long

  "<p>
  In SOFT,
  second-order functions are mimicked
  by first-order functions that reference
  explicitly designated uninterpreted functions that mimic function variables.
  First-order theorems over these second-order functions
  mimic second-order theorems universally quantified over function variables.
  Instances of second-order functions and theorems
  are systematically generated
  by replacing function variables with functions.
  Theorem instances are proved automatically,
  via automatically generated
  <see topic='@(url acl2::functional-instantiation)'>functional
  instantiations</see>.
  </p>

  <p>
  SOFT does not extend the ACL2 logic.
  It is a library that provides macros to introduce
  function variables,
  second-order functions,
  second-order theorems,
  and instances thereof.
  The macros modify the ACL2 state
  only by submitting sound and conservative events;
  they cannot introduce unsoundness or inconsistency on their own.
  </p>

  <p>
  The
  <a href='http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3'
  >ACL2 Workshop 2015 paper on SOFT</a>
  provides
  and overview of the macros and some simple examples of their use,
  a description of the use of SOFT in program refinement,
  and a discussion of related and future work.
  The presentation of the Workshop talk is available
  <a href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2015/program.html'
  >here</a>.
  The examples from the paper are in
  @('[books]/kestrel/soft/workshop-paper-examples.lisp');
  the examples from the talk that are not in the paper are in
  @('[books]/kestrel/soft/workshop-talk-examples.lisp').
  Some of the content of the paper and presentation
  may become outdated as SOFT is extended and improved over time;
  this manual provides up-to-date information about SOFT.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variables

  :parents (soft)

  :short "Notion of function variable."

  :long

  "<p>
  A function variable is an uninterpreted ACL2 function
  introduced via @(tsee defunvar).
  This macro specifies the arity of the function variable.
  </p>

  <p>
  A function variable is used in
  <see topic='@(url second-order-function)'>second-order functions</see> and
  <see topic='@(url second-order-theorem)'>second-order theorems</see>
  as a placeholder for any function with the same arity.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-functions

  :parents (soft)

  :short "Notion of second-order function."

  :long

  "<p>
  A second-order function is an ACL2 function
  that <see topic='@(url function-variable-dependency)'>depends</see>
  on one or more <see topic='@(url function-variable)'>function variables</see>
  and that is introduced via
  @(tsee defun2), @(tsee defchoose2), or @(tsee defun-sk2).
  These macros specify the function parameters of the second-order function,
  i.e. the function variables that the second-order function depends on.
  </p>

  <p>
  The function variables of the second-order function
  may be replaced by functions of matching arities,
  obtaining a new function that is an
  <see topic='@(url second-order-function-instances)'>instance</see>
  of the second-order function.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorems

  :parents (soft)

  :short "Notion of second-order theorem."

  :long

  "<p>
  A second-order theorem is an ACL2 theorem
  that <see topic='@(url function-variable-dependency)'>depends</see>
  on one or more <see topic='@(url function-variable)'>function variables</see>.
  A second-order theorem is introduced via @(tsee defthm);
  SOFT does not provide macros to introduce second-order theorems.
  </p>

  <p>
  The second-order theorem is universally quantified
  over the function variables that it depends on.
  These function variables may be replaced by functions of matching arities,
  obtaining a new theorem that is an
  <see topic='@(url second-order-theorem-instances)'>instance</see>
  of the second-order theorem.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-function-instances

  :parents (soft)

  :short "Notion of instance of a second-order function."

  :long

  "<p>
  An instance of a second-order function is an ACL2 function
  introduced via @(tsee defun-inst),
  which replaces function variables in a specified second-order function
  with functions with matching arities.
  This macro specifies the replacement as an
  <see topic='@(url function-variable-instantiation)'>instantiation</see>,
  which is applied to the body, measure (if recursive), and guard
  of the second-order function.
  </p>

  <p>
  The new function is second-order if it still depends on function variables,
  otherwise it is first-order.
  The new function is recursive iff
  the second-order function that is being instantiated is recursive;
  in this case,
  @(tsee defun-inst) generates a termination proof for the new function
  that uses a <see topic='@(url acl2::functional-instantiation)'>functional
  instance</see> of the termination theorem
  of the second-order function that is being instantiated.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorem-instances

  :parents (soft)

  :short "Notion of instance of a second-order theorem."

  :long

  "<p>
  An instance of a second-order theorem is an ACL2 theorem
  introduced via @(tsee defthm-inst),
  which replaces function variables in a specified second-order theorem
  with functions of matching arities.
  This macro specifies the replacement as an
  <see topic='@(url function-variable-instantiation)'>instantiation</see>,
  which is applied to the formula of the second-order theorem.
  </p>

  <p>
  The new function is second-order if it still depends on function variables,
  otherwise it is first-order.
  @(tsee defthm-inst) generates a proof for the new theorem
  that uses a <see topic='@(url acl2::functional-instantiation)'>functional
  instance</see> of the second-order theorem that is being instantiated.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-dependency

  :parents (soft)

  :short "Notion of dependency of terms on function variables."

  :long

  "<p>
  A @(see term) depends on
  a <see topic='@(url function-variables)'>function variable</see> @('fvar')
  iff
  @('fvar') occurs in @('term')
  or @('fvar') is a function parameter
  of a <see topic='@(url second-order-functions)'>second-order function</see>
  that occurs in @('term').
  </p>

  <p>
  <i>Example:</i>
  Given
  </p>
  @({
  (defunvar ?f (*) => *)
  (defunvar ?g (*) => *)
  (defun2 h[?f] (?f) (x) ...)
  })
  <p>
  it is the case that @('(h[?f] (?g a))')
  depends exactly on @('?g') and @('?f').
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-instantiation

  :parents (soft)

  :short "Notion of function variable instantiation."

  :long

  "<p>
  A function variable instantiation is
  an <see topic='@(url acl2::alists)'>alist</see>
  </p>
  @({
  ((fvar1 . fun1) ... (fvarN . funN))
  })
  <p>
  where @('N') is a non-negative integer,
  @('fvar1'), ..., @('fvarN') are distinct
  <see topic='@(url function-variables)'>function variables</see>,
  and @('fun1'), ..., @('funN') are functions
  such that each @('funI') has the same arity as the corresponding @('fvarI').
  The @('funI') functions may be
  <see topic='@(url function-variables)'>function variables</see>,
  <see topic='@(url second-order-functions)'>second-order functions</see>,
  or &ldquo;regular&rdquo; first-order functions.
  </p>

  <p>
  An instantiation as above is applied to a @(see term) @('term')
  by replacing each @('fvarI') with @('funI').
  This involves not only explicit occurrences of @('fvarI'),
  but also implicit occurrences as function parameters
  of second-order functions occurring in @('term').
  For the latter kind of occurrences,
  suitable <see topic='@(url second-order-function-instances)'>instances</see>
  of such second-order functions must exist;
  if they do not exist, the application of the instantiation fails.
  </p>

  <p>
  <i>Example:</i>
  Given
  </p>
  @({
  (defunvar ?f (*) => *)
  (defunvar ?g (*) => *)
  (defun2 h[?f] (?f) (x) ...)
  (defun2 k[?f] (?f) (x) ...)
  (defun-inst h[consp] (h[?f] (?f . consp)))
  })
  <p>
  @('((?f . consp) (?g . k[?f]))') is an instantiation,
  and the result of applying it to @('(h[?f] (?g a))')
  is @('(h[consp] (k[?f] a))').
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defunvar

  :parents (function-variables)

  :short "Introduce function variable."

  :long

  "<h3>Form</h3>

  @({
  (defunvar fvar (* ... *) => *)
  })

  <h3>Inputs</h3>

  <p>
  @('fvar')
  </p>
  <blockquote>
  <p>
  A symbol, which names the
  <see topic='@(url function-variables)'>function variable</see>.
  It must be a valid function name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('(* ... *)')
  </p>
  <blockquote>
  <p>
  A list of one or more @('*')s,
  which defines the arity of @('fvar').
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  @({
  (defstub fvar (* ... *) => *)
  })
  <blockquote>
  <p>
  @('fvar') is introduced as an uninterpreted function with the given arity.
  </p>
  </blockquote>

  <h3>Examples</h3>

  @({
  (defunvar ?f (*) => *)
  })
  <blockquote>
  <p>
  A unary function variable.
  </p>
  </blockquote>

  @({
  (defunvar ?g (* *) => *)
  })
  <blockquote>
  <p>
  A binary function variable.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  Starting function variable names with @('?')
  (as in the examples above)
  provides a visual cue for their function variable status.
  However, SOFT does not enforce this naming convention.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun2

  :parents (second-order-functions)

  :short
  "Introduce second-order function
  via a second-order version of @(tsee defun)."

  :long

  "<h3>Form</h3>

  @({
  (defun2 sofun (fvar1 ... fvarN) (var1 ... varM)
    doc-string
    declaration ... declaration
    body)
  })

  <h3>Inputs</h3>

  <p>
  @('sofun')
  </p>
  <blockquote>
  <p>
  A symbol, which names the
  <see topic='@(url second-order-functions)'>second-order function</see>.
  It must be a valid function name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('(fvar1 ... fvarN)')
  </p>
  <blockquote>
  <p>
  A non-empty list without duplicates
  of <see topic='@(url function-variables)'>function variables</see>,
  whose order is immaterial.
  These are the function parameters of @('sofun').
  They must be all and only the function variables that
  the body, measure (if @('sofun') is recursive), and guard
  of @('sofun') <see topic='@(url function-variable-dependency)>depend</see> on.
  </p>
  </blockquote>

  <p>
  @('(var1 ... varM)')
  </p>
  <blockquote>
  <p>
  A list of individual parameters, as in @(tsee defun).
  </p>
  </blockquote>

  <p>
  @('doc-string')
  </p>
  <blockquote>
  <p>
  An optional documentation string, as in @(tsee defun).
  </p>
  </blockquote>

  <p>
  @('declaration ... declaration')
  </p>
  <blockquote>
  <p>
  Zero or more declarations, as in @(tsee defun).
  </p>
  </blockquote>

  <p>
  @('body')
  </p>
  <blockquote>
  <p>
  A defining body, as in @(tsee defun).
  If @('sofun') is recursive, its well-founded relation must be @(tsee o<).
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  @({
  (defun sofun (var1 ... varM)
    doc-string
    declaration ... declaration
    body)
  })
  <blockquote>
  <p>
  @('sofun') is introduced as a first-order function using @(tsee defun),
  removing the list of function parameters.
  </p>
  </blockquote>

  <h3>Examples</h3>

  @({
  (defun2 quad[?f] (?f) (x)
    (?f (?f (?f (?f x)))))
  })
  <blockquote>
  <p>
  A non-recursive function
  that applies its function parameter to its individual parameter four times.
  </p>
  </blockquote>

  @({
  (defun2 all[?p] (?p) (l)
    (cond ((atom l) (null l))
          (t (and (?p (car l)) (all[?p] (cdr l))))))
  })
  <blockquote>
  <p>
  A recursive predicate
  that recognizes @('nil')-terminated lists
  whose elements satisfy the predicate parameter.
  </p>
  </blockquote>

  @({
  (defun2 map[?f][?p] (?f ?p) (l)
    (declare (xargs :guard (all[?p] l)))
    (cond ((endp l) nil)
          (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))
  })
  <blockquote>
  <p>
  A recursive function that homomorphically lifts @('?f')
  to operate on @('nil')-terminated lists whose elements satisfy @('?p').
  The predicate parameter @('?p') only appears in the guard, not in the body.
  </p>
  </blockquote>

  @({
  (defun2 fold[?f][?g] (?f ?g) (bt)
    (cond ((atom bt) (?f bt))
          (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))
  })
  <blockquote>
  <p>
  A generic folding function on values as binary trees.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  Ending second-order function names
  with the function parameters enclosed in square brackets
  (as in the examples above)
  conveys the dependency on the function parameters
  and provides a visual cue for the implicit presence of the function parameters
  when the second-order function is applied
  (see the recursive calls in the examples above).
  However, SOFT does not enforce this naming convention.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defchoose2

  :parents (second-order-functions)

  :short
  "Introduce second-order function
  via a second-order version of @(tsee defchoose)."

  :long

  "<h3>Form</h3>

  @({
  (defchoose2 sofun (bvar1 ... bvarP) (fvar1 ... fvarN) (var1 ... varM)
    body
    :strengthen ...)  ; default nil
  })

  <h3>Inputs</h3>

  <p>
  @('sofun')
  </p>
  <blockquote>
  <p>
  A symbol, which names the
  <see topic='@(url second-order-functions)'>second-order function</see>.
  It must be a valid function name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('(bvar1 ... bvarP)')
  <p>
  <blockquote>
  <p>
  A list of bound variables, as in @(tsee defchoose).
  </p>
  </blockquote>

  <p>
  @('(fvar1 ... fvarN)')
  </p>
  <blockquote>
  <p>
  A non-empty list without duplicates
  of <see topic='@(url function-variables)'>function variables</see>,
  whose order is immaterial.
  These are the function parameters of @('sofun').
  They must be all and only the function variables that the body of @('sofun')
  <see topic='@(url function-variable-dependency)>depends</see> on.
  </p>
  </blockquote>

  <p>
  @('(var1 ... varM)')
  </p>
  <blockquote>
  <p>
  A list of individual parameters of @('sofun'), as in @(tsee defun).
  </p>
  </blockquote>

  <p>
  @('body')
  </p>
  <blockquote>
  <p>
  A defining body, as in @(tsee defchoose).
  </p>
  </blockquote>

  <p>
   @(':strengthen ...')
  </p>
  <blockquote>
  <p>
  An option to strengthen the axiom, as in @(tsee defchoose).
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  @({
  (defchoose2 sofun (bvar1 ... bvarP) (var1 ... varM)
    body
    :strengthen ...)
  })
  <blockquote>
  <p>
  @('sofun') is introduced as a first-order function using @(tsee defchoose),
  removing the list of function parameters.
  </p>
  </blockquote>

  <h3>Examples</h3>

  @({
  (defchoose2 fixpoint[?f] x (?f) ()
    (equal (?f x) x))
  })
  <blockquote>
  <p>
  A function constrained to return a fixed point of @('?f'), if any exists.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  The same naming convention for the functions introduced by @(tsee defun2)
  apply to the functions introduced by @(tsee defchoose2).
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-sk2

  :parents (second-order-functions)

  :short
  "Introduce second-order function
  via a second-order version of @(tsee defun-sk)."

  :long

  "<h3>Form</h3>

  @({
  (defun-sk sofun (fvar1 ... fvarN) (var1 ... varM)
    body
    :rewrite ...
    :quant-ok ...
    :skolem-name ...
    :witness-dcls ...
    :strengthen ...)
  })

  <h3>Inputs</h3>

  <p>
  @('sofun')
  </p>
  <blockquote>
  <p>
  A symbol, which names the
  <see topic='@(url second-order-functions)'>second-order function</see>.
  It must be a valid function name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('(fvar1 ... fvarN)')
  </p>
  <blockquote>
  <p>
  A non-empty list without duplicates
  of <see topic='@(url function-variables)'>function variables</see>,
  whose order is immaterial.
  These are the function parameters of @('sofun').
  They must be all and only the function variables that
  the body and guard of @('sofun')
  <see topic='@(url function-variable-dependency)>depend</see> on.
  </p>
  </blockquote>

  <p>
  @('(var1 ... varM)')
  </p>
  <blockquote>
  <p>
  A list of individual parameters of @('sofun'), as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
  @('body')
  </p>
  <blockquote>
  <p>
  A defining body, as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
  @(':rewrite ...')
  </p>
  <blockquote>
  <p>
  An option to customize the rewrite rule, as in @(tsee defun-sk).
  If a term is supplied,
  it must <see topic='@(url function-variable-dependency)>depend</see> on
  the same function variables that
  @('body') <see topic='@(url function-variable-dependency)>depends</see> on.
  </p>
  </blockquote>

  <p>
  @(':quant-ok ...')
  </p>
  <blockquote>
  <p>
  An option to allow @(tsee acl2::forall) and @(tsee acl2::exists)
  in the matrix of @('body'),
  as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
  @(':skolem-name ...')
  </p>
  <blockquote>
  <p>
  An option to customize the name of the witness function,
  as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
  @(':witness-dcls ...')
  </p>
  <blockquote>
  <p>
  An option to customize the declarations of @('sofun'), as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
   @(':strengthen ...')
  </p>
  <blockquote>
  <p>
  An option to strengthen the axiom introduced by @(tsee defchoose),
  as in @(tsee defun-sk).
  </p>
  </blockquote>

  <p>
  Currently @(tsee defun-sk2) does not support a @(':thm-name') option
  as in @(tsee defun-sk).
  Support for @(':thm-name') will be added to @(tsee defun-sk2).
  </p>

  <h3>Generated Events</h3>

  @({
  (defun-sk sofun (var1 ... varM)
    body
    :rewrite ...
    :quant-ok ...
    :skolem-name ...
    :witness-dcls ...
    :strengthen ...)
  })
  <blockquote>
  <p>
  @('sofun') is introduced as a first-order function using @(tsee defun-sk),
  removing the list of function parameters.
  </p>
  </blockquote>

  <h3>Examples</h3>

  @({
  (defun-sk2 injective[?f] (?f) ()
    (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))
  })
  <blockquote>
  <p>
  A predicate that recognizes injective functions.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  The same naming convention for the functions introduced by @(tsee defun2)
  apply to the functions introduced by @(tsee defun-sk2).
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-inst

  :parents (second-order-function-instances)

  :short "Introduce function by instantiating a second-order functions."

  :long

  "<h3>Form</h3>

  @({
  (defun-inst fun (fvar1 ... fvarN)
    (sofun (ffvar1 . fun1) ... (ffvarM . funM))
    :verify-guards ...
    :skolem-name ...
    :rewrite ...)
  })

  <h3>Inputs</h3>

  <p>
  @('fun')
  </p>
  <blockquote>
  <p>
  A symbol, which names the new function obtained by
  <see topic='@(url second-order-function-instances)'>instantiating</see>
  @('sofun').
  It must be a valid function name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('sofun')
  </p>
  <blockquote>
  <p>
  Name of the second-order function to instantiate.
  </p>
  </blockquote>

  <p>
  @('(fvar1 ... fvarN)')
  </p>
  <blockquote>
  <p>
  An optional non-empty list without duplicates
  of <see topic='@(url function-variables)'>function variables</see>,
  whose order is immaterial.
  These are the function parameters of the instance @('fun') of @('sofun').
  They must be all and only the function variables that
  the body, measure (if recursive), and guard (if present)
  of @('fun') <see topic='@(url function-variable-dependency)>depend</see> on.
  (The guard is absent iff @('sofun') was introduced via @(tsee defchoose2).)
  </p>
  <p>
  If the list of function parameters is present,
  @('fun') is a second-order function;
  otherwise, it is a first-order function.
  The function parameters @('fvar1'), ..., @('fvarN') of @('fun')
  are generally unrelated to the function parameters of @('sofun').
  </p>

  <p>
  @('((ffvar1 . fun1) ... (ffvarM . funM))')
  </p>
  <blockquote>
  <p>
  An <see topic='@(url function-variable-instantiation)'>instantiation</see>,
  which specifies how to generate @('fun') from @('sofun').
  The function variables @('ffvar1'), ..., @('ffvarM')
  must be function parameters of @('sofun').
  </p>
  </blockquote>

  <p>
  @(':verify-guards')
  </p>
  <blockquote>
  <p>
  An optional flag to attempt or omit guard verification of @('fun').
  This may be present only if @('sofun') was introduced via @(tsee defun2).
  The default is @('t').
  </p>
  <p>
  In general it is not possible to verify the guards
  of an instance of a second-order function
  from the guard theorem of the second-order function,
  because function variables have guard @('t')
  but may be replaced with function with stricter guards.
  Since @(tsee defun-inst) currently does not provide
  an option to supply guard verification hints for @('fun'),
  @(':verify-guards nil') may be used to defer
  the guard verification of @('fun')
  when it is not accomplished automatically (i.e. without hints).
  (An option to supply guard verification hints
  will be added to @(tsee defun-inst).)
  </p>
  </blockquote>

  <p>
  @(':skolem-name')
  </p>
  <blockquote>
  <p>
  An option to customize the name of the witness function of @('fun').
  This may be present only if @('sofun') was introduced via @(tsee defun-sk2).
  If present, it is passed to the @(tsee defun-sk) generated for @('fun').
  </p>
  </blockquote>

  <p>
  @(':rewrite')
  </p>
  <blockquote>
  <p>
  An option to customize the rewrite rule of @('fun').
  This may be present only if @('sofun') was introduced via @(tsee defun-sk2).
  If present, it is passed to the @(tsee defun-sk) generated for @('fun').
  If a term is supplied,
  it must <see topic='@(url function-variable-dependency)>depend</see> on
  the same function variables that the body of @('fun')
  <see topic='@(url function-variable-dependency)>depends</see> on;
  in particular, if @('fun') is a first-order function,
  the term supplied as rewrite rule must not depend on any function variables.
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  <p>
  One of the following:
  </p>
  <ul>
    <li>
    @({
    (defun2 fun (fvar1 ... fvarN) ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defun2)
    and @('fun') is a second-order function
    (i.e. the list @('(fvar1 ... fvarN)') is present).
    The body, measure (if recursive), and guard of @('fun')
    are obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body, measure (if recursive), and guard of @('sofun').
    If @('fun') is recursive,
    its termination proof uses
    a <see topic='@(url acl2::functional-instantiation)'>functional
    instance</see> of the termination theorem of @('sofun').
    </p>
    </li>
    <li>
    @({
    (defun fun ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defun2)
    and @('fun') is a first-order function
    (i.e. the list @('(fvar1 ... fvarN)') is absent).
    The body, measure (if recursive), and guard of @('fun')
    are obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body, measure (if recursive), and guard of @('sofun').
    If @('fun') is recursive,
    its termination proof uses
    a <see topic='@(url acl2::functional-instantiation)'>functional
    instance</see> of the termination theorem of @('sofun').
    </p>
    </li>
    <li>
    @({
    (defchoose2 fun (bvar1 ... bvarP) (fvar1 ... fvarN) ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defchoose2)
    and @('fun') is a second-order function
    (i.e. the list @('(fvar1 ... fvarN)') is present).
    The body of @('fun')
    is obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body of @('sofun').
    </p>
    </li>
    <li>
    @({
    (defchoose fun (bvar1 ... bvarP) ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defchoose2)
    and @('fun') is a first-order function
    (i.e. the list @('(fvar1 ... fvarN)') is absent).
    The body of @('fun')
    is obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body of @('sofun').
    </p>
    </li>
    <li>
    @({
    (defun-sk2 fun (fvar1 ... fvarN) ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defun-sk2)
    and @('fun') is a second-order function
    (i.e. the list @('(fvar1 ... fvarN)') is present).
    The body and guard of @('fun')
    are obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body and guard of @('sofun').
    </p>
    </li>
    <li>
    @({
    (defun-sk fun ...)
    })
    <p>
    if @('sofun') was introduced via @(tsee defun-sk2)
    and @('fun') is a first-order function
    (i.e. the list @('(fvar1 ... fvarN)') is absent).
    The body and guard of @('fun')
    are obtained by
    <see topic='@(url function-variable-instantiation)'>applying
    the instantiation</see>
    to the body and guard of @('sofun').
    </p>
    </li>
  </ul>

  <h3>Examples</h3>

  @({
  (defun2 quad[?f] (?f) (x) ; example from defun2 manual page
    (?f (?f (?f (?f x)))))
  (defun wrap (x) (list x))
  (defun-inst quad[wrap]
    (quad[?f] (?f . wrap)))
  })
  <blockquote>
  <p>
  Given @('wrap') that wraps a value into a singleton list,
  @('quad[wrap]') wraps a value four times.
  </p>
  </blockquote>

  @({
  (defun2 all[?p] (?p) (l) ; example from defun2 manual page
    (cond ((atom l) (null l))
          (t (and (?p (car l)) (all[?p] (cdr l))))))
  (defun octetp (x) (and (natp x) (< x 256)))
  (defun-inst all[octetp]
    (all[?p] (?p . octetp)))
  })
  <blockquote>
  <p>
  Given @('octetp') that recognizes octets,
  @('all[octetp]') recognizes @('nil')-terminated lists of octets.
  </p>
  </blockquote>

  @({
  (defun2 map[?f][?p] (?f ?p) (l) ; example from defun2 manual page
    (declare (xargs :guard (all[?p] l)))
    (cond ((endp l) nil)
          (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))
  (defun-inst map[code-char][octetp]
    (map[?f][?p] (?f . code-char) (?p . octetp)))
  })
  <blockquote>
  <p>
  Given @('octetp') as in the earlier example,
  and given @(tsee code-char) that translates octets to characters,
  @('map[code-char][octetp]') translates
  lists of octets to lists of characters.
  The replacement @(tsee code-char) of @('?f')
  induces the replacement @('octetp') of @('?p'),
  because the guard of @(tsee code-char) is (equivalent to) @('octectp').
  The creation of the @('map[code-char][octetp]') instance of @('map[?f][?p]')
  needs the instance @('all[octetp]') of @('all[?p]') (in the guard),
  created as in the earlier example.
  </p>
  </blockquote>

  @({
  (defun2 fold[?f][?g] (?f ?g) (bt) ; example from defun2 manual page
    (cond ((atom bt) (?f bt))
          (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))
  (defun-inst fold[nfix][binary-+]
    (fold[?f][?g] (?f . nfix) (?g . binary-+)))
  })
  <blockquote>
  <p>
  @('fold[nfix][binary-+]') adds up all the natural numbers in a tree,
  coercing other values to 0.
  </p>
  </blockquote>

  @({
  (defchoose2 fixpoint[?f] x (?f) () ; example from defchoose2 manual page
    (equal (?f x) x))
  (defun twice (x) (* 2 (fix x)))
  (defun-inst fixpoint[twice]
    (fixpoint[?f] (?f . twice)))
  })
  <blockquote>
  <p>
  Given @('twice') that doubles a value,
  @('fixpoint[twice]') is a function constrained to return
  the (only) fixed point 0 of @('twice').
  </p>
  </blockquote>

  @({
  (defun-sk2 injective[?f] (?f) () ; example from defun-sk2 manual page
    (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))
  (defun-inst injective[quad[?f]] (?f)
    (injective[?f] (?f . quad[?f])))
  })
  <blockquote>
  <p>
  @('injective[quad[?f]]') recognizes functions
  whose four-fold application is injective.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  If the name of the second-order function that is being instantiated
  follows the naming convention described for
  @(tsee defun2), @(tsee defchoose2), and @(tsee defun-sk2),
  the name of the instance can be obtained
  by replacing the names of the function variables between square brackets
  with the names of the replacing functions in the instantiation
  (as in the examples above).
  This conveys the idea of applying the second-order function
  to the functions that replace the function variables.
  However, SOFT does not enforce this naming convention.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defthm-2nd-order

  :parents (second-order-theorems)

  :short "Introduce second-order theorem."

  :long

  "<h3>Form</h3>

  @({
  (defthm sothm
    formula
    :rule-classes ...
    :instructions ...
    :hints ...
    :otf-flg ...)
  })

  <p>
  This is a normal @(tsee defthm).
  SOFT does not provide macros for introducing second-order theorems.
  </p>

  <h3>Inputs</h3>

  <p>
  @('sothm')
  </p>
  <blockquote>
  <p>
  Name of the
  <see topic='@(url second-order-theorems)'>second-order theorem</see>,
  as in @(tsee defthm).
  </p>
  </blockquote>

  <p>
  @('formula')
  </p>
  <blockquote>
  <p>
  Formula of the theorem, as in @(tsee defthm).
  If @('formula') <see topic='@(url function-variable-dependency)'>depends</see>
  on some <see topic='@(url function-variables)'>function variables</see>,
  @('sothm') is a second-order theorem.
  </p>
  </blockquote>

  <p>
  @(':rule-classes')
  </p>
  <blockquote>
  <p>
  Rule classes of the theorem, as in @(tsee defthm).
  </p>
  </blockquote>

  <p>
  @(':instructions')
  </p>
  <blockquote>
  <p>
  Proof checker instructions to prove the theorem, as in @(tsee defthm).
  </p>
  </blockquote>

  <p>
  @(':hints')
  </p>
  <blockquote>
  <p>
  Hints to prove the theorem, as in @(tsee defthm).
  </p>
  </blockquote>

  <p>
  @(':otf-flg')
  </p>
  <blockquote>
  <p>
  &lsquo;Onward Thru the Fog&rsquo; flag, as in @(tsee defthm).
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  <p>
  The @(tsee defthm) itself.
  </p>

  <h3>Examples</h3>

  @({
  (defun2 map[?f][?p] (?f ?p) (l) ; example from defun2 manual page
    (declare (xargs :guard (all[?p] l)))
    (cond ((endp l) nil)
          (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))
  (defthm len-of-map[?f][?p]
    (equal (len (map[?f][?p] l)) (len l)))
  })
  <blockquote>
  <p>
  The theorem shows that
  the homomorphic lifting of @('?f') to lists of @('?p') values
  preserves the length of the list,
  for every function @('?f') and predicate @('?p').
  </p>
  </blockquote>

  @({
  (defun-sk2 injective[?f] (?f) () ; example from defun-sk2 manual page
    (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))
  (defthm injective[quad[?f]]-when-injective[?f]
    (implies (injective[?f]) (injective[quad[?f]]))
    :hints ...)
  })
  <blockquote>
  <p>
  The theorem shows that the four-fold application of an injective function
  is injective.
  </p>
  </blockquote>

  @({
  (defun2 fold[?f][?g] (?f ?g) (bt) ; example from defun2 manual page
    (cond ((atom bt) (?f bt))
          (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))
  (defunvar ?io (* *) => *)
  (defun-sk2 atom-io[?f][?io] (?f ?io) ()
    (forall x (implies (atom x) (?io x (?f x))))
    :rewrite :direct)
  (defun-sk2 consp-io[?g][?io] (?g ?io) ()
    (forall (x y1 y2)
            (implies (and (consp x) (?io (car x) y1) (?io (cdr x) y2))
                     (?io x (?g y1 y2))))
    :rewrite :direct)
  (defthm fold-io[?f][?g][?io]
    (implies (and (atom-io[?f][?io]) (consp-io[?g][?io]))
             (?io x (fold[?f][?g] x))))
  })
  <blockquote>
  <p>
  Given @('?io') for an abstract input/output relation,
  @('atom-io[?f][?io]') that recognizes functions @('?f')
  that satisfy the input/output relation on @(see atom)s,
  @('consp-io[?g][?io]') that recognizes functions @('?g')
  that satisfy the input/output relation on @(tsee cons) pairs
  when the arguments are valid outputs
  for the @(tsee car) and @(tsee cdr) components,
  the theorem shows that
  the generic folding function on binary trees
  satisfies the input/output relation
  when its function parameters satisfy the predicates just introduced.
  </p>
  </blockquote>

  <h3>Naming Conventions</h3>

  <p>
  Including in the name of a second-order theorem, between square brackets,
  the function variables that the theorem depends on,
  makes the dependency more explicit when referencing the theorem.
  This naming convention may arise naturally
  when the name of the theorem includes names of second-order functions
  that follow the analogous naming convention
  (as in the @('len-of-map[?f][?p]') example above),
  or it may be explicitly followed when choosing the name of the theorem
  (as in the @('fold-io[?f][?g][?io]') example above).
  However, SOFT does not enforce this naming convention.
  </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defthm-inst

  :parents (second-order-theorem-instances)

  :short "Introduce theorem by instantiating a second-order theorem."

  :long

  "<h3>Form</h3>

  @({
  (defthm-inst thm
    (sothm (fvar1 . fun1) ... (fvarN . funN))
    :rule-classes ...)
  })

  <h3>Inputs</h3>

  <p>
  @('thm')
  </p>
  <blockquote>
  <p>
  A symbol, which names the new theorem obtained by
  <see topic='@(url second-order-theorem-instances)'>instantiating</see>
  @('sothm').
  It must be a valid theorem name that is not already in use.
  </p>
  </blockquote>

  <p>
  @('sothm')
  </p>
  <blockquote>
  <p>
  Name of the second-order theorem to instantiate.
  </p>
  </blockquote>

  <p>
  @('((fvar1 . fun1) ... (fvarN . funN))')
  </p>
  <blockquote>
  <p>
  An <see topic='@(url function-variable-instantiation)'>instantiation</see>,
  which specifies how to generate @('thm') from @('sothm').
  @('sothm') must <see topic='@(url function-variable-dependency)>depend</see>
  on at least the function variables @('fvar1'), ..., @('fvarN').
  </p>
  </blockquote>

  <p>
  @(':rule-classes')
  </p>
  <blockquote>
  <p>
  An option to specify the rule classes of @('thm').
  </p>
  </blockquote>

  <h3>Generated Events</h3>

  @({
  (defthm thm
    formula
    ... ; proof
    :rule-classes ...)
  })
  <blockquote>
  <p>
  @('thm') is introduced as a theorem,
  whose formula @('formula') is obtained by
  <see topic='@(url function-variable-instantiation)'>applying
  the instantiation</see> to the formula of @('sothm').
  The proof uses
  a <see topic='@(url acl2::functional-instantiation)'>functional
  instance</see> of @('sothm').
  If @(':rule-classes') is supplied to @(tsee defthm-inst),
  its value is used for @('thm');
  otherwise, its value is copied from @('sothm').
  </p>
  </blockquote>

  <h3>Examples</h3>

  @({
  (defun2 map[?f][?p] (?f ?p) (l) ; example from defun2 manual page
    (declare (xargs :guard (all[?p] l)))
    (cond ((endp l) nil)
          (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))
  (defun-inst map[code-char][octetp] ; example from defun-inst manual page
    (map[?f][?p] (?f . code-char) (?p . octetp)))
  (defthm len-of-map[?f][?p] ; example from defthm-2nd-order manual page
    (equal (len (map[?f][?p] l)) (len l)))
  (defthm-inst len-of-map[code-char][octetp]
    (len-of-map[?f][?p] (?f . code-char) (?p . octetp)))
  })
  <blockquote>
  <p>
  The theorem shows that @('map[code-char][octetp]')
  preserves the length of the list.
  </p>
  </blockquote>

  @({
  (defun2 quad[?f] (?f) (x) ; example from defun2 manual page
    (?f (?f (?f (?f x)))))
  (defun-sk2 injective[?f] (?f) () ; example from defun-sk2 manual page
    (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))
  (defun-inst injective[quad[?f]] (?f) ; example from defun-inst manual page
    (injective[?f] (?f . quad[?f])))
  (defun wrap (x) (list x)) ; example from defun-inst manual page
  (defthm ; example from defthm-2nd-order manual page
    injective[quad[?f]]-when-injective[?f]
    (implies (injective[?f]) (injective[quad[?f]]))
    :hints ...)
  (defun-inst injective[quad[wrap]] ; needed by defthm-inst below
    (injective[quad[?f]] (?f . wrap)))
  (defun-inst injective[wrap] ; needed by defthm-inst below
    (injective[?f] (?f . wrap)))
  (defthm-inst injective[quad[wrap]]-when-injective[wrap]
    (injective[quad[?f]]-when-injective[?f] (?f . wrap)))
  })
  <blockquote>
  <p>
  The theorem shows that @('quad[wrap]') is injective if @('wrap') is.
  </p>
  </blockquote>")
