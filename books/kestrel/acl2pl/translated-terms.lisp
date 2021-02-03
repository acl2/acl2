; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "values")

(include-book "kestrel/std/basic/good-pseudo-termp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (std::deflist good-pseudo-term-listp (acl2::x)
   :guard (pseudo-term-listp acl2::x)
   (good-pseudo-termp acl2::x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ translated-terms
  :parents (acl2-programming-language)
  :short "A formalization of ACL2 translated terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2 " (xdoc::seetopic "acl2::term" "terms") " may be
     untranslated (i.e. user-facing) or translated (i.e. internal).
     Here we formalize translated terms,
     which we essentially regard as
     abstract syntax of the ACL2 programming language.
     We may also formalize untranslated terms at some point,
     but for now it seems that translated terms should suffice
     for an initial formalization of the ACL2 programming language.")
   (xdoc::p
    "We formalize translated terms as free algebraic structures,
     without the " (xdoc::seetopic "acl2::world" "world") "-related constraints
     (e.g. that all function symbols are in the world),
     and even without some of the constraints included in @(tsee pseudo-termp)
     (e.g. that the number of actual arguments of a lambda call
     matches the number of parameters of the lambda expression).
     These well-formedness constraints may be formalized separately.")
   (xdoc::p
    "We use (free) fixtypes to formalize translated terms.
     As noted above, these fixtypes are a bit larger than @(tsee pseudo-termp).
     Thus, the fixtypes introduced here differ slightly from "
    (xdoc::seetopic "acl2::pseudo-term-fty" "the pseudo-term fixtypes")
    ", which are consistent with @(tsee pseudo-termp)
     and also include an explicit notion of `null' term."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes tterms

  (fty::deftagsum tterm
    :short "Fixtype of translated terms."
    :long
    (xdoc::topstring-p
     "A translated term is
      a variable (any symbol),
      a (quoted) constant (of any value), or
      a function call.
      The latter consists of a function (see @(tsee tfunction))
      and a list of zero or more argument terms.
      We do not constrain here the number of argument terms
      to match the number of formal parameters of the lambda expression,
      when the function is a lambda expression.")
    (:variable ((name symbol-value)))
    (:constant ((value value)))
    (:call ((function tfunction) (arguments tterm-list)))
    :pred ttermp)

  (fty::deftagsum tfunction
    :short "Fixtype of translated functions."
    :long
    (xdoc::topstring-p
     "The `translated' adjective refers to the fact that
      this is a function in a translated term (see @(tsee tterm)).
      A translated function is a named function (any symbol)
      or a lambda expression;
      the latter consists of zero or more parameters (any symbols)
      and a body (any term).
      We do not constrain a named function to differ from the symbol @('quote');
      the type @(tsee tterm) has a separate constructor for quoted constants.")
    (:named ((name symbol-value)))
    (:lambda ((parameters symbol-value-list) (body tterm)))
    :pred tfunctionp)

  (fty::deflist tterm-list
    :short "Fixtype of lists of translated terms."
    :elt-type tterm
    :true-listp t
    :elementp-of-nil nil
    :pred tterm-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist tterm-case-constant-listp (x)
  :guard (tterm-listp x)
  :short "Lift @('(tterm-case ... :constant)') to lists."
  :long
  (xdoc::topstring-p
   "This checks if all the terms in a list are quoted constants.")
  (tterm-case x :constant)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tterm-constant-list ((values value-listp))
  :returns (terms tterm-listp)
  :short "Lift @(tsee tterm-constant) to lists."
  (cond ((endp values) nil)
        (t (cons (tterm-constant (car values))
                 (tterm-constant-list (cdr values)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection tterm-constant-list->value-list (x)
  :guard (and (tterm-listp x)
              (tterm-case-constant-listp x))
  :returns (values value-listp)
  :short "Lift @(tsee tterm-constant->value) to lists."
  (tterm-constant->value x)
  ///
  (fty::deffixequiv tterm-constant-list->value-list
    :args ((x tterm-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption maybe-tterm
  tterm
  :short "Fixtype of translated terms and @('nil')."
  :pred maybe-ttermp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines lift-term
  :short "Lift pseudo-terms to the meta level."

  (define lift-term ((term pseudo-termp))
    :guard (good-pseudo-termp term)
    :returns (tterm ttermp)
    (b* (((when (variablep term)) (tterm-variable (lift-symbol term)))
         ((when (fquotep term)) (tterm-constant (lift-value (unquote term))))
         (args (lift-term-list (fargs term)))
         (fn (ffn-symb term))
         (tfn (if (symbolp fn)
                  (tfunction-named (lift-symbol fn))
                (tfunction-lambda (lift-symbol-list (lambda-formals fn))
                                  (lift-term (lambda-body fn))))))
      (tterm-call tfn args)))

  (define lift-term-list ((terms pseudo-term-listp))
    :guard (good-pseudo-term-listp terms)
    :returns (terms tterm-listp)
    (cond ((endp terms) nil)
          (t (cons (lift-term (car terms))
                   (lift-term-list (cdr terms))))))

  :verify-guards nil ; done below
  ///
  (verify-guards lift-term
    :hints (("Goal" :in-theory (enable good-pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines tterm-free-vars
  :short "Set of free variables in a (translated) term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Even though ACL2 internally closes all lambda expressions,
     in our formalization of translated terms we do assume or enforce that.
     In fact, we want to have more flexibility,
     and allow non-closed lambda expression.
     Thus, the free variables of a lambda expression,
     as common in other languages,
     are the ones in the body minus the formal parameters."))

  (define tterm-free-vars ((term ttermp))
    :returns (vars symbol-value-setp)
    (tterm-case term
                :variable (set::insert term.name nil)
                :constant nil
                :call (set::union (tfunction-free-vars term.function)
                                  (tterm-list-free-vars term.arguments)))
    :measure (tterm-count term))

  (define tfunction-free-vars ((fun tfunctionp))
    :returns (vars symbol-value-setp)
    (tfunction-case fun
                    :named nil
                    :lambda (set::difference (tterm-free-vars fun.body)
                                             (set::mergesort fun.parameters)))
    :measure (tfunction-count fun))

  (define tterm-list-free-vars ((terms tterm-listp))
    :returns (vars symbol-value-setp)
    (cond ((endp terms) nil)
          (t (set::union (tterm-free-vars (car terms))
                         (tterm-list-free-vars (cdr terms)))))
    :measure (tterm-list-count terms))

  :verify-guards nil ; done below
  ///
  (verify-guards tterm-free-vars)

  (fty::deffixequiv-mutual tterm-free-vars))
