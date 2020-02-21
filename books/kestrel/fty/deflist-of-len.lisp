; FTY -- Fixed-Length List Fixtype Generator
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu)
;          Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc deflist-of-len

  :parents (fty-extensions fty deflist)

  :short "Introduce a <see topic='@(url fty)'>fixtype</see> of
          lists of a specified length."

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "@(tsee deflist) introduces fixtypes of lists of arbitrary lengths.
     Given such a fixtype, the macro @('deflist-of-len') introduces
     a fixtype of those lists that have a specified length,
     along with some theorems that relate
     the recognizers, fixers, and equivalences of the two fixtypes.")

   (xdoc::p
    "The lists may be true or dotted, depending on
     the @(':true-listp') option used in @(tsee deflist).
     The macro @('deflist-of-len') preserves that option.")

   (xdoc::p
    "Future versions of this macro could support
     richer constraints on list length than equality with a certain value,
     e.g. introduce fixtypes of lists of lengths below a certain value.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(deflist-of-len type"
    "                :list-type ..."
    "                :length ..."
    "                :pred ..."
    "                :fix ..."
    "                :equiv ..."
    "                :parents ..."
    "                :short ..."
    "                :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype."))

   (xdoc::desc
    "@(':list-type')"
    (xdoc::p
     "A symbol that names a fixtype previously introduced via @(tsee deflist).
      This is the fixtype of the lists of arbitrary lengths,
      which are a superset of the lists of the generated fixtype.")
    (xdoc::p
     "The recognizer, fixer, and equivalence of the list fixtype
      must be all guard-verified.
      Let @('list-pred'), @('list-fix') and @('list-equiv')
      be their names.")
    (xdoc::p
     "This input must be supplied; there is no default."))

   (xdoc::desc
    "@(':length')"
    (xdoc::p
     "A non-negative integer that specifies the length of the lists.")
    (xdoc::p
     "This input must be supplied; there is no default."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol that specifies the name of the recognizer for @('type').
      If this is @('nil') (the default),
      the name of the recognizer is @('type') followed by @('-p')."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol that specifies the name of the fixer for @('type').
      If this is @('nil') (the default),
      the name of the fixer is @('type') followed by @('-fix')."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol that specifies the name of the equivalence for @('type').
      If this is @('nil') (the default),
      the name of the equivalence is @('type') followed by @('-equiv')."))

   (xdoc::desc
    (list
     "@(':parents')"
     "@(':short')"
     "@(':long')")
    (xdoc::p
     "These, if present, are added to
      the XDOC topic generated for the fixtype."))

   (xdoc::h3 "Generated Events")

   (xdoc::desc
    "@('pred')"
    (xdoc::p
     "The recognizer for the fixtype, guard-verified."))

   (xdoc::desc
    "@('booleanp-of-pred')"
    (xdoc::p
     "A rewrite rule saying that @('pred') is boolean-valued."))

   (xdoc::desc
    (list
     "@('list-pred-when-pred-rewrite')"
     "@('list-pred-when-pred-forward')")
    (xdoc::p
     "A rewrite rule and a forward chaining rule
      saying that a value satisfies @('list-pred')
      when it satisfies @('pred')."))

   (xdoc::desc
    "@('len-when-pred-tau')"
    (xdoc::p
     "A tau system rule saying that if a value satisfies @('pred')
      then its length is the one specified by @(':length')."))

   (xdoc::desc
    "@('fix')"
    (xdoc::p
     "The fixer for the fixtype, guard-verified.")
    (xdoc::p
     "It fixes values outside of @('pred') by applying
      first @(tsee take) with the number specified by @(':length')
      and then @('list-fix') to the result."))

   (xdoc::desc
    "@('pred-of-fix')"
    (xdoc::p
     "A rewrite rule saying that @('fix') always returns
      a value that satisfies @('pred')."))

   (xdoc::desc
    "@('fix-when-pred')"
    (xdoc::p
     "A rewrite rule saying that @('fix') disappears
      when its argument satisfies @('pred')."))

   (xdoc::desc
    (list
     "@('type')"
     "@('equiv')")
    (xdoc::p
     "The fixtype, via a call of @(tsee fty::deffixtype)
      that also introduces the equivalence @('equiv')."))

   (xdoc::p
    "The above items are generated with XDOC documentation.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ deflist-of-len-implementation
  :parents (deflist-of-len)
  :short "Implementation of @(tsee deflist-of-len)."
  :order-subtopics t
  :default-parent t)

(defruled deflist-of-len-support-lemma
  :short "Support lemma for generated fixing theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the events generated by @(tsee deflist-of-len),
     proving that the fixer returns a value that satisifes the recognizer
     involves showing that @(tsee take) returns a list of length
     equal to the first argument of @(tsee take).
     This is not readily provable from the built-in definition of @(tsee take),
     but it is proved in @(see acl2::std/lists/take).
     To avoid implicitly including that file
     when including this file for @(tsee deflist-of-len),
     we locally include that file and provide the theorem here,
     so that it can be used in the generated theorem."))
  (equal (len (take n x)) (nfix n)))

(define deflist-of-len-fn (type
                           list-type
                           length
                           pred
                           fix
                           equiv
                           parents
                           short
                           long
                           (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Events generated by @(tsee deflist-of-len)."
  :long
  (xdoc::topstring-p
   "For now we only perform partial validation of the inputs.
    Future implementations may perform a more thorough validation.")
  (b* (;; validate the TYPE input:
       ((unless (symbolp type))
        (raise "The TYPE input must be a symbol, ~
                but it is ~x0 instead." type))
       ;; validate the :LIST-TYPE input:
       ((unless (symbolp list-type))
        (raise "The :LIST-TYPE input must be a symbol, ~
                but it is ~x0 instead." list-type))
       (fty-table (get-fixtypes-alist wrld))
       (fty-info (find-fixtype list-type fty-table))
       ((unless fty-info)
        (raise "The :LIST-TYPE input ~x0 must name a fixtype, ~
                but it does not." list-type))
       ;; retrieve the recognizer and fixer of the existing list type:
       (list-pred (fixtype->pred fty-info))
       (list-fix (fixtype->fix fty-info))
       ;; validate the :LENGTH input:
       ((unless (natp length))
        (raise "The :LENGTH input must be a non-negative integer, ~
                but it is ~x0 instead." length))
       ;; validate the :PRED input:
       ((unless (symbolp pred))
        (raise "The :PRED input must be a symbol, ~
                but it is ~x0 instead." pred))
       ;; validate the :FIX input:
       ((unless (symbolp fix))
        (raise "The :FIX input must be a symbol, ~
                but it is ~x0 instead." fix))
       ;; validate the :EQUIV input:
       ((unless (symbolp equiv))
        (raise "The :EQUIV input must be a symbol, ~
                but it is ~x0 instead." equiv))
       ;; package for the generated theorem and variable names:
       (pkg (symbol-package-name type))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn type "-P")))
       (fix (or fix (acl2::add-suffix-to-fn type "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn type "-EQUIV")))
       ;; names of the generated theorems:
       (booleanp-of-pred (acl2::packn-pos (list 'booleanp-of- pred)
                                          pkg-witness))
       (list-pred-when-pred-rewrite (acl2::packn-pos (list list-pred
                                                           '-when-
                                                           pred
                                                           '-rewrite)
                                                     pkg-witness))
       (list-pred-when-pred-forward (acl2::packn-pos (list list-pred
                                                           '-when-
                                                           pred
                                                           '-forward)
                                                     pkg-witness))
       (len-when-pred-tau (acl2::packn-pos (list 'len-when- pred '-tau)
                                           pkg-witness))
       (pred-of-fix (acl2::packn-pos (list pred '-of- fix)
                                     pkg-witness))
       (fix-when-pred (acl2::packn-pos (list fix '-when- pred)
                                       pkg-witness))
       ;; variable to use in the generated functions and theorems:
       (x (intern-in-package-of-symbol "X" pkg-witness))
       ;; reference to the fixtype for the generated XDOC documentation:
       (type-ref (concatenate 'string
                              "@(tsee "
                              (acl2::string-downcase (symbol-package-name type))
                              "::"
                              (acl2::string-downcase (symbol-name type))
                              ")"))
       ;; generated events:
       (pred-event
        `(define ,pred (,x)
           :parents (,type)
           :short ,(concatenate 'string "Recognizer for " type-ref ".")
           (and (,list-pred ,x)
                (equal (len ,x) ,length))
           :no-function t
           ///
           (defrule ,booleanp-of-pred
             (booleanp (,pred ,x)))
           (defrule ,list-pred-when-pred-rewrite
             (implies (,pred ,x)
                      (,list-pred ,x)))
           (defrule ,list-pred-when-pred-forward
             (implies (,pred ,x)
                      (,list-pred ,x))
             :rule-classes :forward-chaining)
           (defrule ,len-when-pred-tau
             (implies (,pred ,x)
                      (equal (len ,x) ,length))
             :rule-classes :tau-system)))
       (fix-event
        `(define ,fix ((,x ,pred))
           :parents (,type)
           :short ,(concatenate 'string "Fixer for " type-ref ".")
           (mbe :logic (if (,pred ,x)
                           ,x
                         (,list-fix (take ,length ,x)))
                :exec ,x)
           :no-function t
           ///
           (defrule ,pred-of-fix
             (,pred (,fix ,x))
             :enable (,pred deflist-of-len-support-lemma)
             :disable take)
           (defrule ,fix-when-pred
             (implies (,pred ,x)
                      (equal (,fix ,x) ,x)))))
       (type-event
        `(defsection ,type
           ,@(and parents (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (fty::deffixtype ,type
             :pred ,pred
             :fix ,fix
             :equiv ,equiv
             :define t
             :forward t))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       ,pred-event
       ,fix-event
       ,type-event)))

(defsection deflist-of-len-macro-definition
  :short "Definition of the @(tsee deflist-of-len) macro."
  :long "@(def deflist-of-len)"
  (defmacro deflist-of-len (type
                            &key
                            list-type
                            length
                            pred
                            fix
                            equiv
                            parents
                            short
                            long)
    `(make-event (deflist-of-len-fn
                   ',type
                   ',list-type
                   ',length
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,short
                   ,long
                   (w state)))))
