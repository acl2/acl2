; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "dynamic-function-environments")
(include-book "dynamic-struct-environments")
(include-book "screens")
(include-book "curve-parameterization")

(include-book "kestrel/number-theory/prime" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-environments
  :parents (dynamic-semantics)
  :short "Dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo code executes in the context of information including
     the values stored in the variables and constants that may be accessed,
     the functions that may be called,
     and so on.
     This information is captured by the notion of dynamic environment,
     which is formalized here.")
   (xdoc::p
    "Fixtype names for dynamic environments and their components
     include parts @('dinfo') and @('denv'),
     which stand for `dynamic information' and `dynamic environment'.
     Compare with "
    (xdoc::seetopic "static-environments" "static environments")
    "."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var/const-dinfo
  :short "Fixtype of dynamic information about variables and constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the information associated to a variable or constant name
     in a dynamic environment.
     The information consists of the value stored in the variable or constant,
     and a flag indicating whether it is a variable or a constant.")
   (xdoc::p
    "Note that Leo has no undefined or null value:
     when a variable comes into existence,
     it immediately has a value.
     Thus, it is appropriate for this variable information
     to always have a value.")
   (xdoc::p
    "This fixtype is the dynamic counterpart of @(tsee var/const-sinfo)."))
  ((value value)
   (constp bool))
  :pred var/const-dinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption var/const-dinfo-option
  var/const-dinfo
  :short "Fixtype of optional
          dynamic information about variables and constants."
  :pred var/const-dinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap vcscope-dinfo
  :short "Fixtype of dynamic information about
          scopes of variables and constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "During execution, variable and constant scopes are entered and exited.
     Within a function,
     each @('if') branch, each @('for') body, and each block is a new scope.
     When a function is called, its body is also a new scope.
     Thus, there is a stack of scopes,
     pushed and popped as scopes are entered and exited.")
   (xdoc::p
    "A scope of variables and constants is formalized as a finite map
     from identifiers to information about variables and constants.
     Each pair in the map corresponds to a variable or constant,
     where the key is the name.")
   (xdoc::p
    "A stack of scopes is represented as a list of these finite maps.
     The @(tsee car) of the list is the top of the stack,
     @(tsee cons) is push, and @(tsee cdr) is pop."))
  :key-type identifier
  :val-type var/const-dinfo
  :pred vcscope-dinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist vcscope-dinfo-list
  :short "Fixtype of lists of dynamic information about
          scopes of variables and constants."
  :elt-type vcscope-dinfo
  :true-listp t
  :elementp-of-nil t
  :pred vcscope-dinfo-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum vcscope-dinfo-option
  :short "Fixtype of optional dynamic information about
          scopes of variables and constants."
  (:some ((get vcscope-dinfo)))
  (:none ())
  :pred vcscope-dinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum vcscope-dinfo-list-option
  :short "Fixtype of optional lists of dynamic information about
          lists of scopes of variables and constants."
  (:some ((get vcscope-dinfo-list)))
  (:none ())
  :pred vcscope-dinfo-list-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vcscope-dinfo-result
  :short "Fixtype of errors and dynamic information about
          scopes of variables and constants."
  :ok vcscope-dinfo
  :pred vcscope-dinfo-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vcscope-dinfo-option-result
  :short "Fixtype of errors and
          optional dynamic information about
          scopes of variables and constants."
  :ok vcscope-dinfo-option
  :pred vcscope-dinfo-option-resultp
  :prepwork ((local (in-theory (enable vcscope-dinfo-option-kind)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult vcscope-dinfo-list-result
  :short "Fixtype of errors and
          lists of dynamic information about
          scopes of variables and constants."
  :ok vcscope-dinfo-list
  :pred vcscope-dinfo-list-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod call-dinfo
  :short "Fixtype of dynamic information about function calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "Expressions and statements are executed
     in the context of executing bodies of functions;
     that is, the expressions and statements are from those bodies.
     When a function calls another function, its body is executed,
     and control is returned to the calling function:
     thus, there is a stack of function calls.
     The elements of the stack are frames, in compiler terminology.")
   (xdoc::p
    "The dynamic information about a function call
     consists of the name of the function
     and a stack (i.e. list) of scopes.
     The scope at the bottom of the stack is the one for the function body,
     and the scopes above it correspond to smaller scopes within the body,
     based on where execution goes within the body.")
   (xdoc::p
    "When a function is executed, only the variables and constants
     in the scopes for the function can be accessed.
     Variables and constants in scopes for other function calls
     are not accessible.
     This would be the case also for different calls of the same function,
     if Leo allowed recursion
     (which it does not currently, but it could in the future).")
   (xdoc::p
    "The call stack is represented as a list of values of this fixtype.
     The @(tsee car) of the list is the top of the stack,
     @(tsee cons) is push, and @(tsee cdr) is pop.")
   (xdoc::p
    "Looking at the call stack, the variable and constant scopes
     are organized in a stack of stacks:
     the outer stack is the call stack,
     while the inner stacks are the ones for the function bodies."))
  ((fun identifier)
   (scopes vcscope-dinfo-list))
  :pred call-dinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist call-dinfo-list
  :short "Fixtype of lists of dynamic information about function calls."
  :elt-type call-dinfo
  :true-listp t
  :elementp-of-nil nil
  :pred call-dinfo-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod denv
  :short "Fixtype of dynamic environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment includes
     a call stack,
     a function environment,
     a struct environment,
     and a screen;
     it also includes the curve that parameterizes Leo.
     More components might be added in the future;
     for instance, if global variables and constants were added to Leo,
     then we could add here a dynamic variable and constant scope."))
  ((call-stack call-dinfo-list)
   (functions function-denv)
   (structs struct-denv)
   (screen screen)
   (curve curve))
  :tag :denv
  :pred denvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption denv-option
  denv
  :short "Fixtype of optional dynamic environments."
  :pred denv-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult denv-result
  :short "Fixtype of errors and dynamic environments."
  :ok denv
  :pred denv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-var/const-dinfo-from-scope ((name identifierp)
                                        (scope vcscope-dinfop))
  :returns (dinfo var/const-dinfo-optionp
                  :hints (("Goal" :in-theory (enable var/const-dinfo-optionp))))
  :short "Get the information about a variable or constant from a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if there is no variable of constant with that name."))
  (cdr (omap::assoc (identifier-fix name) (vcscope-dinfo-fix scope)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-var/const-dinfo-from-scope-list ((name identifierp)
                                             (scopes vcscope-dinfo-listp))
  :returns (dinfo var/const-dinfo-optionp)
  :short "Get the information about a variable or constant
          from a list of scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when looking up a variable or constant
     in the stack of scopes for a function call.
     Recall that @(tsee car) is the top of the stack,
     so we search by @(tsee cdr)ing down the list."))
  (b* (((when (endp scopes)) nil)
       (dinfo (get-var/const-dinfo-from-scope name (car scopes)))
       ((when dinfo) dinfo))
    (get-var/const-dinfo-from-scope-list name (cdr scopes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-var/const-dinfo ((name identifierp) (env denvp))
  :returns (dinfo var/const-dinfo-optionp)
  :short "Get the information about a variable a constant
          from a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look through the scopes in the top call of the call stack.
     If the call stack is empty, the variable or constant is not found."))
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) nil)
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call)))
    (get-var/const-dinfo-from-scope-list name scopes))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var/const-dinfo-to-scope ((name identifierp)
                                      (info var/const-dinfop)
                                      (scope vcscope-dinfop))
  :returns (new-scope vcscope-dinfop)
  :short "Add dynamic information about a new variable or constant to a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used after checking that the variable or constant is indeed new.
     We should probably add a guard to that effect here."))
  (omap::update (identifier-fix name)
                (var/const-dinfo-fix info)
                (vcscope-dinfo-fix scope))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var/const-dinfo ((name identifierp)
                             (info var/const-dinfop)
                             (env denvp))
  :returns (new-env denv-optionp)
  :short "Add dynamic information about a new variable or constant
          to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') when the call stack is empty
     or when the scope stack of the top call is empty."))
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) nil)
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call))
       ((when (endp scopes)) nil)
       (top-scope (car scopes))
       (new-top-scope (add-var/const-dinfo-to-scope name info top-scope))
       (new-scopes (cons new-top-scope (cdr scopes)))
       (new-top-call (change-call-dinfo top-call :scopes new-scopes))
       (new-calls (cons new-top-call (cdr calls)))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-var/const-dinfo-in-scope ((name identifierp)
                                         (info var/const-dinfop)
                                         (scope vcscope-dinfop))
  :returns (new-scope vcscope-dinfo-optionp)
  :short "Update the dynamic information for a variable or constant
          in a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return `none' if no variable or constant with that name is found.")
   (xdoc::p
    "Note that this may turn a constant into a variable or vice versa.
     However, this operation is never used in that way."))
  (if (consp (omap::assoc (identifier-fix name)
                          (vcscope-dinfo-fix scope)))
      (vcscope-dinfo-option-some
       (omap::update (identifier-fix name)
                     (var/const-dinfo-fix info)
                     (vcscope-dinfo-fix scope)))
    (vcscope-dinfo-option-none))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-var/const-dinfo-in-scope-list ((name identifierp)
                                              (info var/const-dinfop)
                                              (scopes vcscope-dinfo-listp))
  :returns (new-scopes vcscope-dinfo-list-optionp)
  :short "Update the dynamic information for a variable or constant
          in a list of scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return `none' if we run out of scopes."))
  (b* (((when (endp scopes)) (vcscope-dinfo-list-option-none))
       (scope (car scopes))
       (new-scope (update-var/const-dinfo-in-scope name info scope))
       ((when (vcscope-dinfo-option-case new-scope :some))
        (vcscope-dinfo-list-option-some
         (cons (vcscope-dinfo-option-some->get new-scope)
               (vcscope-dinfo-list-fix (cdr scopes)))))
       (new-scopes (update-var/const-dinfo-in-scope-list name
                                                         info
                                                         (cdr scopes)))
       ((when (vcscope-dinfo-list-option-case new-scopes :none))
        (vcscope-dinfo-list-option-none))
       (new-scopes (vcscope-dinfo-list-option-some->get new-scopes)))
    (vcscope-dinfo-list-option-some
     (cons scope new-scopes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define update-var/const-dinfo ((name identifierp)
                                (info var/const-dinfop)
                                (env denvp))
  :returns (new-env denv-optionp)
  :short "Update the dynamic information for a variable or constant
          in a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') when the call stack is empty
     or no variable or constant with that name is found in the top frame."))
  (b* ((calls (denv->call-stack env))
       ((when (endp calls)) nil)
       (top-call (car calls))
       (scopes (call-dinfo->scopes top-call))
       ((when (endp scopes)) nil)
       (new-scopes (update-var/const-dinfo-in-scope-list name info scopes))
       ((when (vcscope-dinfo-list-option-case new-scopes :none)) nil)
       (new-scopes (vcscope-dinfo-list-option-some->get new-scopes))
       (new-top-call (change-call-dinfo top-call :scopes new-scopes))
       (new-calls (cons new-top-call (cdr calls)))
       (new-env (change-denv env :call-stack new-calls)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-denv ((curve curvep))
  :returns (env denvp)
  :short "Initial dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the prime and the curve,
     which are passed as parameters to this ACL2 function.")
   (xdoc::p
    "All the other components of the environment are empty."))
  (make-denv :call-stack nil
             :functions (init-function-denv)
             :structs (init-struct-denv)
             :screen (init-screen)
             :curve curve)
  :hooks (:fix))
