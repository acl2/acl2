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

(include-book "type-maps-for-struct-components")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-environments
  :parents (static-semantics)
  :short "Static environments of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantic requirements on Leo constructs
     (expressions, statements, etc.)
     are checked in the context of information (e.g. types) about
     entities in scope that can be referenced in the constructs being checked.
     This information is captured by the notion of static environment,
     which is formalized here.")
   (xdoc::p
    "In compiler terminology, these are symbol tables.")
   (xdoc::p
    "Fixtype names defined here include parts @('sinfo') and @('senv'),
     which stand for `static information' and `static environment'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod var/const-sinfo
  :short "Fixtype of static information for variables and constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the information that a static environment associates
     to an identifier that is either a variable or a constant in scope.
     The information consists of a type,
     and a flag indicating if it is a constant or not (i.e. a variable).")
   (xdoc::p
    "As far as variables and constants are concerned,
     instead of defining this fixtype,
     we could instead, in @(tsee ident-sinfo),
     have separate summands for variables and constants
     that just contain a type.
     However, we can use this fixtype to capture
     the parameter information for functions:
     this is why we define this fixtype this way,
     and consequently @(tsee ident-sinfo) has
     just one summand for both variables and constants."))
  ((type type)
   (constp bool))
  :tag :var/const-sinfo
  :pred var/const-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var/const-sinfo-list
  :short "Fixtype of lists of static information for variables and constants."
  :elt-type var/const-sinfo
  :true-listp t
  :elementp-of-nil nil
  :pred var/const-sinfo-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption var/const-sinfo-option
  var/const-sinfo
  :short "Fixtype of optional static information for variables and constants."
  :pred var/const-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-sinfo
  :short "Fixtype of static information for functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the information that a static environment associates
     to an identifier that is a function in scope.
     The information consists of
     a list of types and constant flags for the function inputs
     and a type for the function output."))
  ((inputs var/const-sinfo-list)
   (output type))
  :tag :fun-sinfo
  :pred function-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption function-sinfo-option
  function-sinfo
  :short "Fixtype of optional static information about functions."
  :pred function-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct-sinfo
  :short "Fixtype of static information about struct types."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this only consists of information about the components,
     organized as a type map, from component names to their types.
     The finite map structure is adequate
     because components have unique names.")
   (xdoc::p
    "This static information for struct types may be extended
     with information about associated constants and functions."))
  ((components type-map))
  :tag :struct-sinfo
  :pred struct-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption struct-sinfo-option
  struct-sinfo
  :short "Fixtype of optional static information for struct types."
  :pred struct-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ident-sinfo
  :short "Fixtype of static information for identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the information that a static environment associates
     to identifiers in scope, which may be
     variables, constants, functions, or struct types.
     There are three kinds of identifier information:
     one for variables and constants (see @(tsee var/const-sinfo));
     one for function (see @(tsee function-sinfo));
     and one for struct types (see @(tsee struct-sinfo))."))
  (:var/const ((get var/const-sinfo)))
  (:function ((get function-sinfo)))
  (:struct ((get struct-sinfo)))
  :pred ident-sinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption ident-sinfo-option
  ident-sinfo
  :short "Fixtype of optional static information for identifiers."
  :pred ident-sinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap ident-senv
  :short "Fixtype of static environments for identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a finite map from identifiers to identifier static information.")
   (xdoc::p
    "In Leo, variables, constants, functions, and struct types
     share the same name space:
     for example, a function and a variable in scope cannot have the same name.
     Thus, it si appropriate the use a single finite map from identifiers
     to information about variables, constants, functions, and struct types.")
   (xdoc::p
    "Leo disallows shadowing: for example, a variable cannot be declared
     with the same name as a variable already in scope.
     Thus, we do not need to take into account variable and constant scopes,
     and can use a single finite map from identifiers to information."))
  :key-type identifier
  :val-type ident-sinfo
  :pred ident-senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv
  :short "Fixtype of static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently this is just a wrapper for identifier static environments,
     but it may contain additional information for future versions of Leo.
     This is why we introduce this wrapping here."))
  ((identifiers ident-senv))
  :tag :senv
  :pred senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption senv-option
  senv
  :short "Fixtype of optional static environments."
  :pred senv-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult senv-result
  :short "Fixtype of errors and static environments."
  :ok senv
  :pred senv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-ident-sinfo ((id identifierp) (env senvp))
  :returns (info ident-sinfo-optionp
                 :hints (("Goal" :in-theory (enable ident-sinfo-optionp))))
  :short "Retrieve information about an identifier from a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the identifier is not found."))
  (cdr (omap::assoc (identifier-fix id) (senv->identifiers env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-var/const-sinfo ((v/c identifierp) (env senvp))
  :returns (info var/const-sinfo-optionp)
  :short "Retrieve information about a variable or constant
          from a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the variable or constant is not found.
     This includes the case that the identifier is in the environment
     but it does not refers to a variable or constant."))
  (b* ((info (get-ident-sinfo v/c env))
       ((unless info) nil))
    (ident-sinfo-case info
                      :var/const info.get
                      :function nil
                      :struct nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-sinfo ((fun identifierp) (env senvp))
  :returns (info function-sinfo-optionp)
  :short "Retrieve information about a function from a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the function is not found.
     This includes the case that the identifier is in the environment
     but it does not refer to a function."))
  (b* ((info (get-ident-sinfo fun env))
       ((unless info) nil))
    (ident-sinfo-case info
                      :var/const nil
                      :function info.get
                      :struct nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-struct-sinfo ((circ identifierp) (env senvp))
  :returns (info struct-sinfo-optionp)
  :short "Retrieve information about a struct type from a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the function is not found.
     This includes the case that the identifier is in the environment
     but it does not refer to a struct type"))
  (b* ((info (get-ident-sinfo circ env))
       ((unless info) nil))
    (ident-sinfo-case info
                      :var/const nil
                      :function nil
                      :struct info.get))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-ident-sinfo ((id identifierp) (info ident-sinfop) (env senvp))
  :returns (new-env senv-optionp)
  :short "Add information about an identifier to a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the identifier is already in the environment."))
  (b* ((id (identifier-fix id))
       (ienv (senv->identifiers env))
       ((when (consp (omap::assoc id ienv))) nil)
       (new-ienv (omap::update id (ident-sinfo-fix info) ienv))
       (new-env (make-senv :identifiers new-ienv)))
    new-env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-var/const-sinfo ((v/c identifierp)
                             (info var/const-sinfop)
                             (env senvp))
  :returns (new-env senv-optionp)
  :short "Add information about a variable or constant to a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return @('nil') if the identifier is already in the environment."))
  (add-ident-sinfo v/c (ident-sinfo-var/const info) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-function-sinfo ((fun identifierp)
                            (info function-sinfop)
                            (env senvp))
  :returns (new-env senv-optionp)
  :short "Add information about a function to a static environment."
  (add-ident-sinfo fun (ident-sinfo-function info) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-struct-sinfo ((circ identifierp)
                           (info struct-sinfop)
                           (env senvp))
  :returns (new-env senv-optionp)
  :short "Add information about a struct type to a static environment."
  (add-ident-sinfo circ (ident-sinfo-struct info) env)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-senv ()
  :returns (env senvp)
  :short "Initialize a static environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "The environment is initially empty."))
  (make-senv :identifiers nil))
