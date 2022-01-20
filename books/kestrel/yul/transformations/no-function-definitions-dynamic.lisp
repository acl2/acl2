; Yul Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "no-function-definitions")

(include-book "../language/dynamic-semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ no-function-definitions-in-dynamic-semantics
  :parents (no-function-definitions)
  :short "The condition in which function definitions are elsewhere,
          applied to entities in the dynamic semntics."
  :long
  (xdoc::topstring
   (xdoc::p
    "We extend the @('...-nofunp') predicates
     defined in @(see no-function-definitions)
     to some of the dynamic semantics entities.
     This extension serves to take advantage of this condition
     in proofs of dynamic correctness of transformations
     that assume that the code satisfies the condition.
     In fact, we prove theorems that are used in such proofs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo-nofunp ((funinfo funinfop))
  :returns (yes/no booleanp)
  :short "Check that a function information
          has no function definitions in the function's body."
  (block-nofunp (funinfo->body funinfo))
  :hooks (:fix)
  ///

  (defruled block-nofunp-of-funinfo->body
    (equal (block-nofunp (funinfo->body funinfo))
           (funinfo-nofunp funinfo))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funinfo-nofunp-of-funinfo-for-fundef
  (equal (funinfo-nofunp (funinfo-for-fundef fundef))
         (fundef-nofunp fundef))
  :enable (funinfo-nofunp
           funinfo-for-fundef
           fundef-nofunp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funscope-nofunp ((funscope funscopep))
  :returns (yes/no booleanp)
  :short "Check that a function scope
          has no function definitions in the functions' bodies."
  (or (not (mbt (funscopep funscope)))
      (omap::empty funscope)
      (and (b* (((mv & funinfo) (omap::head funscope)))
             (funinfo-nofunp funinfo))
           (funscope-nofunp (omap::tail funscope))))
  :hooks (:fix)
  ///

  (defrule funinfo-nofunp-of-cdr-of-in-when-funscope-nofunp
    (implies (and (funscopep funscope)
                  (funscope-nofunp funscope)
                  (consp (omap::in fun funscope)))
             (funinfo-nofunp (cdr (omap::in fun funscope)))))

  (defrule funscope-nofunp-of-update
    (implies (and (funscopep funscope)
                  (funscope-nofunp funscope)
                  (funinfop funinfo)
                  (funinfo-nofunp funinfo))
             (funscope-nofunp (omap::update fun funinfo funscope)))
    :enable (funscopep
             omap::update
             omap::head
             omap::tail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funscope-funp-of-funscope-for-fundefs
  (implies (and (fundef-list-nofunp fundefs)
                (not (resulterrp (funscope-for-fundefs fundefs))))
           (funscope-nofunp (funscope-for-fundefs fundefs)))
  :enable (funscope-for-fundefs
           funscope-nofunp
           fundef-list-nofunp
           funscopep-when-funscope-resultp-and-not-resulterrp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist funenv-nofunp (x)
  :guard (funenvp x)
  :short "Check that a function environment
          has no function definitions in the functions' bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check each scope in the environment."))
  (funscope-nofunp x)
  :true-listp nil
  :elementp-of-nil t
  ///
  (fty::deffixequiv funenv-nofunp
    :args ((x funenvp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funinfo+funenv-nofunp ((funinfoenv funinfo+funenv-p))
  :returns (yes/no booleanp)
  :short "Check that
          a pair consisting of function information and a function environment
          has no function definitions in the functions' bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check each component."))
  (and (funinfo-nofunp (funinfo+funenv->info funinfoenv))
       (funenv-nofunp (funinfo+funenv->env funinfoenv)))
  :hooks (:fix)
  ///

  (defrule funinfo-nofunp-of-funinfo+funenv->info
    (implies (funinfo+funenv-nofunp funinfoenv)
             (funinfo-nofunp (funinfo+funenv->info funinfoenv))))

  (defrule funenv-nofunp-of-funinfo+funenv->env
    (implies (funinfo+funenv-nofunp funinfoenv)
             (funenv-nofunp (funinfo+funenv->env funinfoenv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funinfo+funenv-nofunp-of-find-fun
  :short "Theorem about @(tsee find-fun) and @('...-nofunp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee find-fun) is successful
     on a function environment without function definitions in the bodies,
     the result has no function definitions in the bodies."))
  (implies (and (funenv-nofunp funenv)
                (not (resulterrp (find-fun fun funenv))))
           (funinfo+funenv-nofunp (find-fun fun funenv)))
  :enable (find-fun
           funenv-nofunp
           funinfo+funenv-nofunp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule funenv-nofunp-of-add-funs
  :short "Theorem about @(tsee add-funs) and @('...-nofunp')."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee add-funs) is successful on
     a list of function definitions without nested function definitions
     and a function environment without function definitions in the bodies,
     the result is a function envnrionment
     without function definitions in the bodies.
     That is, this property of the function environment is preserved."))
  (implies (and (fundef-list-nofunp fundefs)
                (funenv-nofunp funenv)
                (not (resulterrp (add-funs fundefs funenv))))
           (funenv-nofunp (add-funs fundefs funenv)))
  :enable add-funs)
