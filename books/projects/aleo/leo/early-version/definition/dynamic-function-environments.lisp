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

(include-book "files")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dynamic-function-environments
  :parents (dynamic-environments)
  :short "Dynamic environments for functions in Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "In Leo, functions are referenced by name when they are called.
     Thus, the dynamic semantics of Leo constructs
     that reference functions by name
     must be defined with respect to information for the function names.
     We capture that via the notion of dynamic environment for functions,
     which associates dynamic information for functions to function names."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod function-dinfo
  :short "Fixtype of dynamic information for functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This captures the information associated to a function
     in a dynamic environment for functions.
     The information consists of
     the inputs of the function
     (well captured by function parameters in the abstract syntax),
     the output type of the function,
     and the body of the function.
     The name of the function is outside this function information,
     so that we can define finite maps: see @(tsee function-denv).")
   (xdoc::p
    "This function information is the same as
     in function definitions in the abstract syntax (see @(tsee fundecl))."))
  ((inputs funparam-list)
   (output type)
   (body statement-list))
  :pred function-dinfop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption function-dinfo-option
  function-dinfo
  :short "Fixtype of optional dynamic information for functions."
  :pred function-dinfo-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap function-denv
  :short "Fixtype of dynamic environments for functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A dynamic environment for functions is a finite map
     from identifiers to dynamic information for functions.
     Each pair in the map corresponds to a function:
     the key is the name and the value is the information."))
  :key-type identifier
  :val-type function-dinfo
  :pred function-denvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum function-denv-option
  :short "Fixtype of optional dynamic environments for functions."
  (:some ((get function-denv)))
  (:none ())
  :pred function-denv-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-function-dinfo ((fun identifierp) (env function-denvp))
  :returns (info? function-dinfo-optionp
                  :hints (("Goal" :in-theory (enable function-dinfo-optionp))))
  :short "Get the information for a function in a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no function with that name in the environment,
     we return @('nil') to indicate an error."))
  (cdr (omap::assoc (identifier-fix fun) (function-denv-fix env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-function-dinfo ((fun identifierp)
                            (info function-dinfop)
                            (env function-denvp))
  :returns (new-env function-denv-optionp)
  :short "Add information for a function to a dynamic environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return `none' if
     there is already a function with the same nme in the environment."))
  (b* ((fun (identifier-fix fun))
       (info (function-dinfo-fix info))
       (env (function-denv-fix env))
       ((when (consp (omap::assoc fun env))) (function-denv-option-none))
       (new-env (omap::update fun info env)))
    (function-denv-option-some new-env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-function-denv ()
  :returns (env function-denvp)
  :short "Initial dynamic function environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is empty."))
  nil)
