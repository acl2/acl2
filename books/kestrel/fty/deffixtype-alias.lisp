; FTY -- Alias Generator
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc deffixtype-alias

  :parents (fty-extensions fty deffixtype)

  :short "Introduce an alias of an existing fixtype."

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Sometimes a fixtype, as well as its recognizer, fixer, and equivalence,
     have names that are appropriate in a general context,
     but that could be made more convenient and readable
     in a more restrictive context.
     For instance, the @(tsee acl2::ubyte4) and @(tsee acl2::ubyte8) fixtypes
     (and their recognizers, fixers, and equivalences)
     are named according to
     a uniform scheme in @(tsee fty::defbyte-standard-instances),
     but in many contexts the names @('nibble') and @('byte')
     would be arguably more convenient.")

   (xdoc::p
    "Instead of defining new fixtypes, recognizers, fixers, and equivalences
     with the desired names,
     and inevitably having to introduce theorems about them,
     it is preferable to introduce and use aliases.
     ACL2 has built-in support to do this for functions,
     via @(tsee add-macro-alias) and @(tsee add-macro-fn).
     For the fixtypes themselves, i.e. for the fixtype names,
     aliases can be actually created via @(tsee deffixtype),
     which simply records (in the ACL2 @(see world))
     the association between the fixtype name
     and its recognizer, fixer, and equivalence:
     by calling @(tsee deffixtype)
     with the aliases for recognizer, fixer, and equivalence,
     we effectively create an alias of the existing fixtype.")

   (xdoc::p
    "This macro automates this process.
     It introduces
     macro aliases for a fixtype's recognizer, fixer, and equivalence,
     along with a new fixtype associated to such aliases,
     which is effectively an alias of the existing fixtype.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(deffixtype-alias alias"
    "  type"
    "  :pred ..."
    "  :fix ..."
    "  :equiv ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('alias')"
    (xdoc::p
     "A symbol to use as the new fixtype alias."))

   (xdoc::desc
    "@('type')"
    (xdoc::p
     "A symbol that names the existing fixtype to alias."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol to use as the new recognizer alias.")
    (xdoc::p
     "If not supplied, the recognizer of the new fixtype
      is the same as the existing fixtype."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol to use as the new fixer alias.")
    (xdoc::p
     "If not supplied, the fixer of the new fixtype
      is the same as the existing fixtype."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol to use as the new equivalence alias.")
    (xdoc::p
     "If not supplied, the equivalence of the new fixtype
      is the same as the existing fixtype."))

   (xdoc::h3 "Generated Events")

   (xdoc::p
    "Macro definitions for the new recognizer, fixer, and equivalence
     (except for those whose corresponding keyword input is not supplied).")

   (xdoc::p
    "Calls of @(tsee add-macro-fn)
     to associate the new recognizer, fixer, and equivalence
     with the existing ones
     (except for those whose corresponding keyword input is not supplied).")

   (xdoc::p
    "A call of @(tsee deffixtype) for the new fixtype.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection deffixtype-alias-implementation
  :parents (deffixtype-alias)
  :short "Implementation of @(tsee deffixtype-alias)."
  :long (xdoc::topstring-@def "deffixtype-alias")

  (define deffixtype-alias-fn (alias type pred fix equiv (wrld plist-worldp))
    :returns (event "A @(tsee pseudo-event-formp).")
    :mode :program
    (b* ((table (get-fixtypes-alist wrld))
         (info (find-fixtype type table))
         ((fixtype info) info)
         (pred-events (and pred
                           `((defmacro ,pred (x) (list ',info.pred x))
                             (add-macro-fn ,pred ,info.pred))))
         (fix-events (and fix
                          `((defmacro ,fix (x) (list ',info.fix x))
                            (add-macro-fn ,fix ,info.fix))))
         (equiv-events (and equiv
                            `((defmacro ,equiv (x y) (list ',info.equiv x y)))))
         (deffixtype-event `(deffixtype ,alias
                              :pred ,(or pred info.pred)
                              :fix ,(or fix info.fix)
                              :equiv ,(or equiv info.equiv))))
      `(encapsulate
         ()
         ,@pred-events
         ,@fix-events
         ,@equiv-events
         ,deffixtype-event)))

  (defmacro deffixtype-alias (alias type &key pred fix equiv)
    `(make-event
      (deffixtype-alias-fn ',alias ',type ',pred ',fix ',equiv (w state)))))
