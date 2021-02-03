; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "errors")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-function-environments
  :parents (atc-dynamic-semantics)
  :short "C function environments for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "C code is executed in the context of function definitions in scope,
     which may be referenced by the code.")
   (xdoc::p
    "Here we formalize a notion of function environment as a finite map
     from function names (i.e. identifiers)
     to information about the function.
     These function environments are used in the dynamic semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-info
  :short "Fixtype of information about a C function in an environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the components of a function definition
     (see @(tsee fundef))
     without the name.
     This is because names are used as keys in a function environment.
     The other components form the value associated to the key."))
  ((params param-decl-list)
   (result tyspecseq)
   (body stmt))
  :pred fun-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fun-info-option
  fun-info
  :short "Fixtype of optional information about a C function in an environment."
  :pred fun-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap fun-env
  :short "Fixtype of function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function environment is a finite map
     from function names (i.e. identifiers)
     to information about the function."))
  :key-type ident
  :val-type fun-info
  :pred fun-envp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult fun-env "function environments")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-fun-env ()
  :returns (fenv fun-envp)
  :short "An irrelevant function environment, usable as a dummy return value."
  (with-guard-checking :none (ec-call (fun-env-fix :irrelevant)))
  ///
  (in-theory (disable (:e irr-fun-env))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-env-lookup ((name identp) (fenv fun-envp))
  :returns (info? fun-info-optionp)
  :short "Look up a function in an environment by name."
  (cdr (omap::in (ident-fix name)
                 (fun-env-fix fenv)))
  :prepwork ((local (in-theory (enable fun-info-optionp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-env-extend ((fundef fundefp) (fenv fun-envp))
  :returns (result fun-env-resultp)
  :short "Extend a function environment with a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the environment already has a function with the same name,
     this operation returns an error."))
  (b* ((fenv (fun-env-fix fenv))
       ((fundef fundef) fundef)
       ((when (fun-env-lookup fundef.name fenv))
        (error (list :duplicate-function-definition fundef.name)))
       (info (make-fun-info :params fundef.params
                            :result fundef.result
                            :body fundef.body)))
    (omap::update fundef.name info fenv))
  :hooks (:fix))
