; SOFT (Second-Order Functions and Theorems) -- Documentation
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft

  :parents (acl2::kestrel-books acl2::macro-libraries acl2::projects)

  :short "SOFT (Second-Order Functions and Theorems)
          is a tool to mimic second-order functions and theorems
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
   <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
   >ACL2-2015 Workshop paper on SOFT</a>
   provides
   an overview of the macros and some simple examples of their use,
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
   The differences between
   the current version of SOFT and the Workshop version of SOFT
   are described <see topic='@(url updates-since-workshop)'>here</see>.
   </p>")

(xdoc::order-subtopics soft nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft-notions

  :parents (soft)

  :short "Notions that the SOFT macros are based on."

  :long

  "<p>
   The macros provided by SOFT are based on the notions
   defined in the sub-topics below.
   </p>")

(xdoc::order-subtopics soft-notions nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft-macros

  :parents (soft)

  :short "Macros provided by SOFT."

  :long

  "<p>
   @(tsee defunvar),
   @(tsee defun2),
   @(tsee defchoose2), and
   @(tsee defun-sk2)
   are wrappers of existing events
   that explicate function variable dependencies
   and record additional information.
   They set the stage for @(tsee defun-inst) and @(tsee defthm-inst).
   </p>

   <p>
   @(tsee defun-inst) provides the ability to concisely generate functions,
   and automatically prove their termination if recursive,
   by specifying replacements of function variables.
   </p>

   <p>
   @(tsee defthm-inst) provides the ability to
   concisely generate and automatically prove theorems,
   by specifying replacements of function variables.
   </p>")

(xdoc::order-subtopics soft-macros nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variables

  :parents (soft-notions)

  :short "Notion of function variable."

  :long

  "<p>
   A function variable is an uninterpreted ACL2 function
   introduced via @(tsee defunvar).
   This macro specifies the arity of the function variable.
   </p>

   <p>
   A function variable is used in
   <see topic='@(url second-order-functions)'>second-order functions</see> and
   <see topic='@(url second-order-theorems)'>second-order theorems</see>
   as a placeholder for any function with the same arity.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-functions

  :parents (soft-notions)

  :short "Notion of second-order function."

  :long

  "<p>
   A second-order function is an ACL2 function
   that <see topic='@(url function-variable-dependency)'>depends</see> on
   one or more <see topic='@(url function-variables)'>function variables</see>
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

(xdoc::order-subtopics second-order-functions nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorems

  :parents (soft-notions)

  :short "Notion of second-order theorem."

  :long

  "<p>
   A second-order theorem is an ACL2 theorem
   that <see topic='@(url function-variable-dependency)'>depends</see> on
   one or more <see topic='@(url function-variables)'>function variables</see>.
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

  :parents (soft-notions)

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
   instance</see> of the
   <see topic='@(url termination-theorem)'>termination theorem</see>
   of the second-order function that is being instantiated.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc second-order-theorem-instances

  :parents (soft-notions)

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
   The new theorem is second-order if it still depends on function variables,
   otherwise it is first-order.
   @(tsee defthm-inst) generates a proof for the new theorem
   that uses a <see topic='@(url acl2::functional-instantiation)'>functional
   instance</see> of the second-order theorem that is being instantiated.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-dependency

  :parents (soft-notions)

  :short "Notion of dependency of terms on function variables."

  :long

  "<p>
   A <see topic='@(url acl2::term)'>term</see> @('term') depends on
   a <see topic='@(url function-variables)'>function variable</see> @('fvar')
   iff
   @('fvar') occurs in @('term')
   or @('fvar') is a function parameter
   of a <see topic='@(url second-order-functions)'>second-order function</see>
   that occurs in @('term').
   </p>

   <h4>Example</h4>

   <p>
   Given
   </p>
   @({
     (defunvar ?f (*) => *)
     (defunvar ?g (*) => *)
     (defun2 h[?f] (?f) (x) ...)
   })
   <p>
   the term @('(h[?f] (?g a))') depends exactly on @('?g') and @('?f').
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc function-variable-instantiation

  :parents (soft-notions)

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
   An instantiation as above is applied
   to a <see topic='@(url acl2::term)'>term</see> @('term')
   by replacing each @('fvarI') with @('funI').
   This involves not only explicit occurrences of @('fvarI'),
   but also implicit occurrences as function parameters
   of second-order functions occurring in @('term').
   For the latter kind of occurrences,
   suitable <see topic='@(url second-order-function-instances)'>instances</see>
   of such second-order functions must exist;
   if they do not exist, the application of the instantiation fails.
   </p>

   <h4>Example:</h4>

   <p>
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
   the alist @('((?f . consp) (?g . k[?f]))') is an instantiation,
   and the result of applying it to the term @('(h[?f] (?g a))')
   is the term @('(h[consp] (k[?f] a))').
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defunvar

  :parents (soft-macros function-variables)

  :short "Introduce function variable."

  :long

  "<h3>General Form</h3>

   @({
     (defunvar fvar (* ... *) => *
       :print ...)
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
     A list of zero or more @('*') signs,
     which defines the arity of @('fvar').
     </p>

     </blockquote>

   <p>
   @(':print ...')
   </p>

     <blockquote>

     <p>
     An option to customize the screen output:
     @(':all') to print all the output;
     @('nil') (the default) to print only any error output.
     </p>

     </blockquote>

   <h3>Generated Events</h3>

   @({
     (defstub fvar (* ... *) => *)
   })

   <p>
   @('fvar') is introduced as an uninterpreted function with the given arity.
   </p>

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; A unary function variable:
     (defunvar ?f (*) => *)
   })

   <h4>Example 2</h4>

   @({
     ;; A unary function variable:
     (defunvar ?p (*) => *)
   })

   <h4>Example 3</h4>

   @({
     ;; A binary function variable:
     (defunvar ?g (* *) => *)
   })

   <h3>Naming Conventions</h3>

   <p>
   Starting function variable names with @('?') (as in the examples above)
   provides a visual cue for their function variable status.
   However, SOFT does not enforce this naming convention.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defun)."

  :long

  "<h3>General Form</h3>

   @({
     (defun2 sofun (fvar1 ... fvarN) (var1 ... varM)
       doc-string
       declaration ... declaration
       body
       :print ...)
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
     the body, measure (if recursive), and guard of @('sofun')
     <see topic='@(url function-variable-dependency)'>depend</see> on.
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

   <p>
   @(':print ...')
   </p>

     <blockquote>

     <p>
     An option to customize the screen output:
     @(':all') to print all the output;
     @('nil') to print only any error output;
     @(':fn-output') (the default) to print only
     the (possibly error) output from the generated @(tsee defun).
     </p>

     </blockquote>

   <h3>Generated Events</h3>

   @({
     (defun sofun (var1 ... varM)
       doc-string
       declaration ... declaration
       body)
   })

   <p>
   @('sofun') is introduced as a first-order function using @(tsee defun),
   removing the list of function parameters.
   </p>

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; A non-recursive function that applies four times
     ;; its function parameter to its individual parameter:
     (defun2 quad[?f] (?f) (x)
       (?f (?f (?f (?f x)))))
   })

   <h4>Example 2</h4>

   @({
   ;; A recursive predicate that recognizes NIL-terminated lists
   ;; whose elements satisfy the predicate parameter:
   (defun2 all[?p] (?p) (l)
     (cond ((atom l) (null l))
           (t (and (?p (car l)) (all[?p] (cdr l))))))
   })

   <h4>Example 3</h4>

   @({
     ;; A recursive function that homomorphically lifts ?F
     ;; to operate on NIL-terminated lists whose elements satisfy ?P:
     (defun2 map[?f][?p] (?f ?p) (l)
       (declare (xargs :guard (all[?p] l)))
       (cond ((endp l) nil)
             (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))
     ;; The predicate parameter ?P only occurs in the guard, not in the body.
   })

   <h4>Example 4</h4>

   @({
     ;; A generic folding function on values as binary trees:
     (defun2 fold[?f][?g] (?f ?g) (bt)
       (cond ((atom bt) (?f bt))
             (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))
   })

   <h3>Naming Conventions</h3>

   <p>
   Ending second-order function names
   with the function parameters enclosed in square brackets
   (as in the examples above)
   conveys the dependency on the function parameters
   and provides a visual cue for the implicit presence
   of the function parameters
   when the second-order function is applied
   (see the recursive calls in the examples above).
   However, SOFT does not enforce this naming convention.
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defchoose2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defchoose)."

  :long

  "<h3>General Form</h3>

   @({
     (defchoose2 sofun (bvar1 ... bvarP) (fvar1 ... fvarN) (var1 ... varM)
       body
       :strengthen ...
       :print ...)
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
   </p>

     <blockquote>
     <p>
     A list of bound variables (or a single variable), as in @(tsee defchoose).
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
     They must be all and only the function variables
     that the body of @('sofun')
     <see topic='@(url function-variable-dependency)'>depends</see> on.
     </p>

     </blockquote>

   <p>
   @('(var1 ... varM)')
   </p>
   <blockquote>
   <p>
   A list of individual parameters of @('sofun'), as in @(tsee defchoose).
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

   <p>
   @(':print ...')
   </p>

     <blockquote>

     <p>
     An option to customize the screen output:
     @(':all') to print all the output;
     @('nil') to print only any error output;
     @(':fn-output') (the default) to print only
     the (possibly error) output from the generated @(tsee defchoose).
     </p>

     </blockquote>

   <h3>Generated Events</h3>

   @({
     (defchoose2 sofun (bvar1 ... bvarP) (var1 ... varM)
       body
       :strengthen ...)
   })

   <p>
   @('sofun') is introduced as a first-order function using @(tsee defchoose),
   removing the list of function parameters.
   </p>

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; A function constrained to return a fixed point of ?F, if any exists:
     (defchoose2 fixpoint[?f] x (?f) ()
       (equal (?f x) x))
   })

   <h3>Naming Conventions</h3>

   <p>
   The same naming convention for the functions introduced by @(tsee defun2)
   apply to the functions introduced by @(tsee defchoose2).
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-sk2

  :parents (soft-macros second-order-functions)

  :short "Introduce second-order function
          via a second-order version of @(tsee defun-sk)."

  :long

  "<h3>General Form</h3>

   @({
     (defun-sk sofun (fvar1 ... fvarN) (var1 ... varM)
       body
       :rewrite ...
       :quant-ok ...
       :skolem-name ...
       :thm-name ...
       :witness-dcls ...
       :strengthen ...
       :print ...)
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
     <see topic='@(url function-variable-dependency)'>depend</see> on.
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
     it must <see topic='@(url function-variable-dependency)'>depend</see> on
     the same function variables that @('body')
     <see topic='@(url function-variable-dependency)'>depends</see> on.
     As in @(tsee defun-sk), this option may be present
     only if the quantifier is universal.
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
   @(':thm-name ...')
   </p>

     <blockquote>

     <p>
     An option to customize the name of the rewrite rule,
     as in @(tsee defun-sk).
     </p>

     </blockquote>

   <p>
   @(':witness-dcls ...')
   </p>

     <blockquote>

     <p>
     An option to customize the declarations of @('sofun'),
     as in @(tsee defun-sk).
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
   @(':print ...')
   </p>

     <blockquote>

     <p>
     An option to customize the screen output:
     @(':all') to print all the output;
     @('nil') to print only any error output;
     @(':fn-output') (the default) to print only
     the (possibly error) output from the generated @(tsee defun-sk).
     </p>

     </blockquote>

   <h3>Generated Events</h3>

   @({
     (defun-sk sofun (var1 ... varM)
       body
       :rewrite ...
       :quant-ok ...
       :skolem-name ...
       :thm-name ...
       :witness-dcls ...
       :strengthen ...)
   })

   <p>
   @('sofun') is introduced as a first-order function using @(tsee defun-sk),
   removing the list of function parameters.
   </p>

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; A predicate that recognizes injective functions:
     (defun-sk2 injective[?f] (?f) ()
      (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))
   })

   <h3>Naming Conventions</h3>

   <p>
   The same naming convention for the functions introduced by @(tsee defun2)
   apply to the functions introduced by @(tsee defun-sk2).
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defun-inst

  :parents (soft-macros second-order-function-instances)

  :short "Introduce function by instantiating a second-order functions."

  :long

  "<h3>General Form</h3>

   @({
     (defun-inst fun (fvar1 ... fvarN)
       (sofun (ffvar1 . fun1) ... (ffvarM . funM))
       :verify-guards ...
       :skolem-name ...
       :thm-name ...
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
     the body, measure (if recursive), and guard (if present) of @('fun')
     <see topic='@(url function-variable-dependency)'>depend</see> on.
     (The guard is absent iff @('sofun') was introduced via @(tsee defchoose2).)
     </p>

     <p>
     If the list of function parameters is present, @('fun') is second-order;
     otherwise, it is first-order.
     The function parameters @('fvar1'), ..., @('fvarN') of @('fun')
     are generally unrelated to the function parameters of @('sofun').
     </p>

     </blockquote>

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
     An optional flag to attempt or omit the guard verification of @('fun').
     This may be present only if @('sofun') was introduced via @(tsee defun2).
     If this flag is absent,
     the guard verification of @('fun') is attempted
     iff @('sofun') is guard-verified.
     </p>

     <p>
     In general it is not possible to verify the guards
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
     will be added to @(tsee defun-inst).)
     </p>

     </blockquote>

   <p>
   @(':skolem-name')
   </p>

     <blockquote>

     <p>
     An option to customize the name of the witness function of @('fun').
     This may be present
     only if @('sofun') was introduced via @(tsee defun-sk2).
     If present, it is passed to the @(tsee defun-sk) generated for @('fun').
     </p>

     </blockquote>

   <p>
   @(':thm-name')
   </p>

     <blockquote>

     <p>
     An option to customize the name of the rewrite rule of @('fun').
     This may be present
     only if @('sofun') was introduced via @(tsee defun-sk2).
     If present, it is passed to the @(tsee defun-sk) generated for @('fun').
     </p>

     </blockquote>

   <p>
   @(':rewrite')
   </p>

     <blockquote>

     <p>
     An option to customize the rewrite rule of @('fun').
     This may be present only if @('sofun') was introduced via @(tsee defun-sk2)
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
     the rewrite rule of @('fun') has the same form as in @('sofun');
     in particular, the function variables in the rewrite rule of @('sofun')
     are instantiated via the instantiation passed to @(tsee defun-inst).
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
     and @('fun') is second-order
     (i.e. the list @('(fvar1 ... fvarN)') is present).
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
     of @('sofun').
     </p>
     </li>

     <li>
     @({
       (defun fun ...)
     })
     <p>
     if @('sofun') was introduced via @(tsee defun2)
     and @('fun') is first-order
     (i.e. the list @('(fvar1 ... fvarN)') is absent).
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
     of @('sofun').
     </p>
     </li>

     <li>
     @({
       (defchoose2 fun (bvar1 ... bvarP) (fvar1 ... fvarN) ...)
     })
     <p>
     if @('sofun') was introduced via @(tsee defchoose2)
     and @('fun') is second-order
     (i.e. the list @('(fvar1 ... fvarN)') is present).
     The body of @('fun')
     is obtained by
     <see topic='@(url function-variable-instantiation)'>applying
     the instantiation</see>
     to the body of @('sofun').
     The @(':strengthen') value of @('fun') is the same as @('sofun').
     </p>
     </li>

     <li>
     @({
       (defchoose fun (bvar1 ... bvarP) ...)
     })
     <p>
     if @('sofun') was introduced via @(tsee defchoose2)
     and @('fun') is first-order
     (i.e. the list @('(fvar1 ... fvarN)') is absent).
     The body of @('fun')
     is obtained by
     <see topic='@(url function-variable-instantiation)'>applying
     the instantiation</see>
     to the body of @('sofun').
     The @(':strengthen') value of @('fun') is the same as @('sofun').
     </p>
     </li>

     <li>
     @({
       (defun-sk2 fun (fvar1 ... fvarN) ...)
     })
     <p>
     if @('sofun') was introduced via @(tsee defun-sk2)
     and @('fun') is second-order
     (i.e. the list @('(fvar1 ... fvarN)') is present).
     The body and guard of @('fun')
     are obtained by
     <see topic='@(url function-variable-instantiation)'>applying
     the instantiation</see>
     to the body and guard of @('sofun').
     The guard of @('fun') is not verified.
     The @(':strengthen') value of @('fun') is the same as @('sofun').
     The @(':quant-ok') value of @('fun') is @('t').
     </p>
     </li>

     <li>
     @({
       (defun-sk fun ...)
     })
     <p>
     if @('sofun') was introduced via @(tsee defun-sk2)
     and @('fun') is first-order
     (i.e. the list @('(fvar1 ... fvarN)') is absent).
     The body and guard of @('fun')
     are obtained by
     <see topic='@(url function-variable-instantiation)'>applying
     the instantiation</see>
     to the body and guard of @('sofun').
     The guard of @('fun') is not verified.
     The @(':strengthen') value of @('fun') is the same as @('sofun').
     The @(':quant-ok') value of @('fun') is @('t').
     </p>
     </li>

   </ul>

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; Apply ?F four times to X:
     (defun2 quad[?f] (?f) (x)
       (?f (?f (?f (?f x)))))

     ;; Wrap a value into a singleton list:
     (defun wrap (x) (list x))

     ;; Wrap a value four times:
     (defun-inst quad[wrap]
       (quad[?f] (?f . wrap)))
   })

   <h4>Example 2</h4>

   @({
     ;; Recognize NIL-terminated lists of values that satisfy ?P:
     (defun2 all[?p] (?p) (l)
       (cond ((atom l) (null l))
             (t (and (?p (car l)) (all[?p] (cdr l))))))

     ;; Recognize octets:
     (defun octetp (x) (and (natp x) (< x 256)))

     ;; Recognize NIL-terminated lists of octets:
     (defun-inst all[octetp]
       (all[?p] (?p . octetp)))
   })

   <h4>Example 3</h4>

   @({
     ;; Homomorphically lift ?F to on NIL-terminated lists of ?P values:
     (defun2 map[?f][?p] (?f ?p) (l)
       (declare (xargs :guard (all[?p] l)))
       (cond ((endp l) nil)
             (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))

     ;; Translate lists of octets to lists of characters:
     (defun-inst map[code-char][octetp]
       (map[?f][?p] (?f . code-char) (?p . octetp)))
     ;; The replacement CODE-CHAR of ?F
     ;; induces the replacement OCTETP of ?P,
     ;; because the guard of CODE-CHAR is (equivalent to) OCTECTP.
     ;; The creation of the MAP[CODE-CHAR][OCTETP] instance of MAP[?F][?P]
     ;; needs the instance ALL[OCTETP) of ALL[?P] (in the guard),
     ;; created as in the earlier example.
   })

   <h4>Example 4</h4>

   @({
     ;; Folding function on binary trees:
     (defun2 fold[?f][?g] (?f ?g) (bt)
       (cond ((atom bt) (?f bt))
             (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))

     ;; Add up all the natural numbers in a tree, coercing other values to 0:
     (defun-inst fold[nfix][binary-+]
       (fold[?f][?g] (?f . nfix) (?g . binary-+)))
   })

   <h4>Example 5</h4>

   @({
     ;; Return a fixed point of ?F, if any exists:
     (defchoose2 fixpoint[?f] x (?f) ()
       (equal (?f x) x))

     ;; Double a value:
     (defun twice (x) (* 2 (fix x)))

     ;; Function constrained to return the (only) fixed point 0 of TWICE:
     (defun-inst fixpoint[twice]
       (fixpoint[?f] (?f . twice)))
   })

   <h4>Example 6</h4>

   @({
     ;; Recognize injective functions:
     (defun-sk2 injective[?f] (?f) ()
       (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))

     ;; Recognize functions whose four-fold application is injective:
     (defun-inst injective[quad[?f]] (?f)
       (injective[?f] (?f . quad[?f])))
   })

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

  :parents (soft-macros second-order-theorems)

  :short "Introduce second-order theorem."

  :long

  "<h3>General Form</h3>

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
     If @('formula')
     <see topic='@(url function-variable-dependency)'>depends</see>
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

   <h4>Example 1</h4>

   @({
     ;; Homomorphically lift ?F to on NIL-terminated lists of ?P values:
     (defun2 map[?f][?p] (?f ?p) (l)
       (declare (xargs :guard (all[?p] l)))
       (cond ((endp l) nil)
             (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))

     ;; The homomorphic lifting of ?F to lists of ?P values
     ;; preserves the length of the list,
     ;; for every function ?F and predicate ?P:
     (defthm len-of-map[?f][?p]
       (equal (len (map[?f][?p] l)) (len l)))
   })

   <h4>Example 2</h4>

   @({
     ;; Recognize injective functions:
     (defun-sk2 injective[?f] (?f) ()
       (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))

     ;; The four-fold application of an injective function is injective:
     (defthm injective[quad[?f]]-when-injective[?f]
       (implies (injective[?f]) (injective[quad[?f]]))
       :hints ...)
   })

   <h4>Example 3</h4>

   @({
     ;; Folding function on binary trees:
     (defun2 fold[?f][?g] (?f ?g) (bt)
       (cond ((atom bt) (?f bt))
             (t (?g (fold[?f][?g] (car bt)) (fold[?f][?g] (cdr bt))))))

     ;; Abstract input/output relation:
     (defunvar ?io (* *) => *)

     ;; Recognize functions ?F that satisfy the input/output relation on atoms:
     (defun-sk2 atom-io[?f][?io] (?f ?io) ()
       (forall x (implies (atom x) (?io x (?f x))))
       :rewrite :direct)

     ;; Recognize functions ?G that satisfy
     ;; the input/output relation on CONSP pairs
     ;; when the arguments are valid outputs for the CAR and CDR components:
     (defun-sk2 consp-io[?g][?io] (?g ?io) ()
       (forall (x y1 y2)
               (implies (and (consp x) (?io (car x) y1) (?io (cdr x) y2))
                        (?io x (?g y1 y2))))
       :rewrite :direct)

     ;; The generic folding function on binary trees
     ;; satisfies the input/output relation
     ;; when its function parameters satisfy the predicates just introduced:
     (defthm fold-io[?f][?g][?io]
       (implies (and (atom-io[?f][?io]) (consp-io[?g][?io]))
                (?io x (fold[?f][?g] x))))
   })

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

  :parents (soft-macros second-order-theorem-instances)

  :short "Introduce theorem by instantiating a second-order theorem."

  :long

  "<h3>General Form</h3>

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
     @('sothm') must
     <see topic='@(url function-variable-dependency)'>depend</see>
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

   <h3>Examples</h3>

   <h4>Example 1</h4>

   @({
     ;; Homomorphically lift ?F to on NIL-terminated lists of ?P values:
     (defun2 map[?f][?p] (?f ?p) (l)
       (declare (xargs :guard (all[?p] l)))
       (cond ((endp l) nil)
             (t (cons (?f (car l)) (map[?f][?p] (cdr l))))))

     ;; Translate lists of octets to lists of characters:
     (defun-inst map[code-char][octetp]
       (map[?f][?p] (?f . code-char) (?p . octetp)))

     ;; The homomorphic lifting of ?F to lists of ?P values
     ;; preserves the length of the list:
     (defthm len-of-map[?f][?p]
       (equal (len (map[?f][?p] l)) (len l)))

     ;; MAP[CODE-CHAR][OCTETP] preserves the length of the list:
     (defthm-inst len-of-map[code-char][octetp]
       (len-of-map[?f][?p] (?f . code-char) (?p . octetp)))
   })

   <h4>Example 2</h4>

   @({
     ;; Apply ?F four times to X:
     (defun2 quad[?f] (?f) (x)
       (?f (?f (?f (?f x)))))

     ;; Recognize injective functions:
     (defun-sk2 injective[?f] (?f) ()
       (forall (x y) (implies (equal (?f x) (?f y)) (equal x y))))

     ;; Recognize functions whose four-fold application is injective:
     (defun-inst injective[quad[?f]] (?f)
       (injective[?f] (?f . quad[?f])))

     ;; Wrap a value into a singleton list:
     (defun wrap (x) (list x))

     ;; The four-fold application of an injective function is injective:
     (defthm injective[quad[?f]]-when-injective[?f]
       (implies (injective[?f]) (injective[quad[?f]]))
       :hints ...)

     ;; Needed by DEFTHM-INST below to apply its instantiation:
     (defun-inst injective[quad[wrap]]
       (injective[quad[?f]] (?f . wrap)))

     ;; Needed by DEFTHM-INST below to apply its instantiation:
     (defun-inst injective[wrap]
       (injective[?f] (?f . wrap)))

     ;; QUAD[WRAP] is injective if WRAP is:
     (defthm-inst injective[quad[wrap]]-when-injective[wrap]
       (injective[quad[?f]]-when-injective[?f] (?f . wrap)))
   })")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc updates-since-workshop

  :parents (soft)

  :short "Updates to SOFT since the ACL2-2015 Workshop."

  :long

  "<h4>Nullary Function Variables</h4>

   <p>
   Nullary function variables (i.e. function variables with arity 0)
   are now allowed.
   </p>

   <h4>Naming Conventions</h4>

   <p>
   For second-order functions and theorems
   that depend on two or more function variables,
   the Workshop paper suggests to use underscores
   to separate the function variables inside the square brackets,
   e.g. @('sofun[?f_?g_?h]').
   This manual instead suggests
   to enclose each function variable in square brackets,
   e.g. @('sofun[?f][?g][?h]').
   </p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft-implementation

  :parents (soft)

  :short "Implementation of SOFT.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft-future-work

  :parents (soft)

  :short "Some possible improvements and extensions to SOFT."

  :long

  "<h4>Mutual Recursion</h4>

   <p>
   SOFT should be extended with the ability to introduce and instantiate
   mutually recursive functions,
   perhaps via a new @('mutual-recursion2') macro.
   </p>

   <h4>Other Well-Founded Relations</h4>

   <p>
   Currently recursive second-order functions
   must use @(tsee o<) as their well-founded relation.
   This could be relaxed, perhaps even to the point of
   allowing second-order well-founded relations.
   </p>

   <h4>Other Function and Theorem Introduction Macros</h4>

   <p>
   Besides second-order versions of
   @(tsee defun), @(tsee defchoose), and @(tsee defun-sk),
   we could add support for second-order versions of
   @(tsee defund), @(tsee defun-nx), @(tsee define), @(tsee defpun),
   and other function introduction events.
   @(tsee defun-inst) would generate the same macros for instances.
   The macros could be called @('defund2'), @('defun-nx2'), etc.
   </p>

   <p>
   Under some conditions, it would make sense for @(tsee defun-inst)
   to instantiate a partial second-order function
   (introduced, say, via a future @('defpun2') macro)
   to a total second-order function (i.e. a @(tsee defun2) or @(tsee defun)),
   when the instantiated @(':domain') or @(':gdomain') restrictions
   are theorems.
   </p>

   <p>
   @(tsee defthm-inst) could also generate instances with the same macros
   from second-order theorems introduced via
   @(tsee defthm), @(tsee defrule), and other theorem introduction events.
   </p>

   <h4>Program Mode</h4>

   <p>
   Currently SOFT only supports logic-mode second-order funcions.
   Supporting program-mode functions as well may be useful.
   </p>

   <h4>Guards of Instances of Second-Order Functions</h4>

   <p>
   It would be useful to allow
   the default guards of instances of second-order functions
   (obtained by instantiating the guards of the second-order functions)
   to be overridden by stronger guards.
   </p>

   <p>
   The <see topic='@(url acl2::guard-theorem)'>guard theorem</see>
   of a second-order function may be useful
   (although not sufficient in general)
   to verifies the guards of instances of the second-order function.
   A mechanism to enable the use of that theorem would be useful.
   </p>

   <p>
   See the future work section of the
   <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
   >Workshop paper</a>
   for a more detailed discussion with examples.
   </p>

   <h4>Lambda Expressions</h4>

   <p>
   Instantiations could be extended to allow function variables
   to be replaces with lambda expressions, besides named functions.
   </p>

   <h4>Transitivity of Instantiations</h4>

   <p>
   Intuitively,
   if @('f') is an instance of @('g')
   and @('g') is an instance of @('h'),
   then @('f') should be an instance of @('h').
   This is currently not supported by @(tsee defun-inst),
   but probably it should be.
   </p>

   <p>
   See the future work section of the
   <a href=\"http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3\"
   >Workshop paper</a>
   for a more detailed discussion with examples.
   </p>

   <h4>More Constraints on Function Variables</h4>

   <p>
   The types of function variables are currently limited to
   <see topic='@(url acl2::signature)'>signatures</see>
   with single-value results and with no stobjs.
   This could be extended to allow multiple-value results and stobjs.
   Instantiations will have to respect these additional type structures.
   </p>

   <p>
   Other than their types, function variables are currently unconstrained.
   In some cases, it may be useful to specify some logical constraints,
   resulting in a constrained function as in non-trivial @(tsee encapsulate)s.
   Instantiations will have to respect these additional constraints.
   </p>

   <p>
   The latter extension would overlap with some existing tools,
   such as @('instance-of-defspec') and @('make-generic-theory').
   Ideally, the functionality of SOFT and those tools would be integrated.
   </p>

   <p>
   Function variables current have guard @('t').
   It may be useful to allow guards to be specified for function variables.
   Instantiations will have to match these guards.
   </p>

   <h4>Automatic Instances</h4>

   <p>
   Currently, when an instantiation is applied to a term,
   the table of instances of second-order functions is consulted
   to find replacements for certain second-order functions,
   and the application of the instantiation fails
   if replacements are not found.
   Thus, all the needed instances must be introduced
   before applying the instantiation.
   SOFT could be extended to generate automatically
   the needed instances of second-order functions.
   </p>

   <p>
   SOFT could also be extended with a macro @('defthm2')
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
   These extensions would reduce the use of explicit @(tsee defthm-inst)s.
   </p>

   <p>
   The convention of including function variables in square brackets
   in the names of second-order functions and theorems,
   could be exploited to name the automatically generated
   function and theorem instances.
   </p>

   <h4>Default Rule Classes</h4>

   <p>
   Currently the default rule classes
   of an instance of a second-order theorem are @('(:rewrite)'),
   but perhaps the default should be the rule classes
   of the second-order theorem that is being instantiated.
   </p>")
