; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax-operations")
(include-book "errors")

(include-book "kestrel/fty/defomap" :dir :system)

; Added 7/1/2021 by Matt K. after 3 successive ACL2(p) certification failures:
(set-waterfall-parallelism nil)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ function-environments
  :parents (language)
  :short "C function environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "C code is executed in the context of function definitions in scope,
     which may be referenced by the code.")
   (xdoc::p
    "Here we formalize a notion of function environment as a finite map
     from function names (i.e. identifiers)
     to information about the functions.
     These function environments are used in the dynamic semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-info
  :short "Fixtype of information about a C function in an environment."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     the components of a function definition (see @(tsee fundef))
     without the name and
     with the type specifier sequence and the declarator
     combined into a type name.
     The names are used as keys in a function environment.
     The other components form the value associated to the key."))
  ((params param-declon-list)
   (result tyname)
   (body block-item-list))
  :pred fun-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption fun-info-option
  fun-info
  :short "Fixtype of optional information about a C function in an environment."
  :pred fun-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-info-from-fundef ((fundef fundefp))
  :returns (finfo fun-infop)
  :short "Create information for a function definition."
  (b* (((fundef fundef) fundef)
       ((mv & params tyname)
        (tyspec+declor-to-ident+params+tyname fundef.tyspec fundef.declor)))
    (make-fun-info :params params
                   :result tyname
                   :body fundef.body))
  :hooks (:fix))

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

(fty::defresult fun-env-result
  :short "Fixtype of errors and function environments."
  :ok fun-env
  :pred fun-env-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fun-env-lookup ((name identp) (fenv fun-envp))
  :returns (info? fun-info-optionp)
  :short "Look up a function in an environment by name."
  (cdr (omap::assoc (ident-fix name)
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
       (name (fundef->name fundef))
       ((when (fun-env-lookup name fenv))
        (reserrf (list :duplicate-function-definition name)))
       (info (fun-info-from-fundef fundef)))
    (omap::update name info fenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-fun-env ((tunit transunitp))
  :returns (result fun-env-resultp)
  :short "Initialize the function environment for a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go though the external declarations that form the translation unit
     and we build the function environment for the function definitions,
     starting from the empty environment."))
  (init-fun-env-aux (transunit->declons tunit) nil)
  :hooks (:fix)

  :prepwork
  ((define init-fun-env-aux ((declons ext-declon-listp) (fenv fun-envp))
     :returns (result fun-env-resultp)
     :parents nil
     (b* (((when (endp declons)) (fun-env-fix fenv))
          (declon (car declons)))
       (ext-declon-case
        declon
        :obj-declon (init-fun-env-aux (cdr declons) fenv)
        :fun-declon (init-fun-env-aux (cdr declons) fenv)
        :tag-declon (init-fun-env-aux (cdr declons) fenv)
        :fundef (b* (((okf fenv) (fun-env-extend declon.get fenv)))
                  (init-fun-env-aux (cdr declons) fenv))))
     :hooks (:fix))))
