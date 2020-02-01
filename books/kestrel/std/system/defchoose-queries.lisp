; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "function-namep")

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defchoose-queries
  :parents (std/system/function-queries defchoose)
  :short "Utilities to query @(tsee defchoose) functions."
  :long
  (xdoc::topstring-p
   "Since @(tsee defchoose) is a primitive event,
    functions introduced via @(tsee defchoose)
    can always be recognized precisely.
    Besides the non-@(tsee defchoose)-specific constituents
    (e.g. formal arguments),
    which can be queried with "
   (xdoc::seetopic "std/system/function-queries" "more general utilities")
   ", these functions have @(tsee defchoose)-specific constituent,
    which can be queried with these @(tsee defchoose) query utilities.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoosep ((fn symbolp) (wrld plist-worldp))
  :returns (axiom "A @(tsee pseudo-termp).")
  :short "Check if a function was introduced via @(tsee defchoose),
          returning the function's constraining axiom if the check succeeds."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check fails, @('nil') is returned.")
   (xdoc::p
    "A function introduced via @(tsee defchoose) is recognizable
     by the presence of the @('defchoose-axiom') property,
     which is the axiom that constrains the function.")
   (xdoc::p
    "This utility causes an error if called on a symbol
     that is not a function symbol."))
  (if (not (function-symbolp fn wrld))
      (raise "The symbol ~x0 does not name a function." fn)
    (getpropc fn 'defchoose-axiom nil wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoose-namep (x (wrld plist-worldp))
  :returns (yes/no booleanp)
  :short "Recognize symbols
          that name functions introduced via @(tsee defchoose)."
  :long
  (xdoc::topstring-p
   "This function is enabled because it is meant as an abbreviation.
    Theorems triggered by this function should be generally avoided.")
  (and (function-namep x wrld)
       (defchoosep x wrld)
       t)
  :enabled t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoose-bound-vars ((fn (defchoose-namep fn wrld))
                              (wrld plist-worldp))
  :returns (bound-vars "A @(tsee symbol-listp).")
  :mode :program
  :short "Bound variables of a function introduced via @(tsee defchoose)."
  :long
  (xdoc::topstring-p
   "The bound variables are in the third element of the @(tsee defchoose) event,
    which is either a single bound variable
    or a non-empty list of bound variables.")
  (let* ((event (get-event fn wrld))
         (bound-var/bound-vars (third event)))
    (if (symbolp bound-var/bound-vars)
        (list bound-var/bound-vars)
      bound-var/bound-vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoose-strengthen ((fn (defchoose-namep fn wrld))
                              (wrld plist-worldp))
  :returns (t/nil "A @(tsee booleanp).")
  :mode :program
  :short "Value of the @(':strengthen') option
          of a function introduced via @(tsee defchoose)."
  :long
  (xdoc::topstring-p
   "If explicitly supplied, the value of the @(':strengthen') option
    is the last element of the @(tsee defchoose) event,
    which consists of seven element in this case.
    If not explicitly supplied,
    the value of the @(':strengthen') option is @('nil'),
    and the @(tsee defchoose) event consists of five elements only.")
  (let ((event (get-event fn wrld)))
    (if (= (len event) 5)
        nil
      (car (last event)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoose-untrans-body ((fn (defchoose-namep fn wrld))
                                (wrld plist-worldp))
  :mode :program
  :short (xdoc::topstring
          (xdoc::seetopic "term" "Untranslated")
          " body of a function introduced via @(tsee defchoose).")
  :long
  (xdoc::topstring-p
   "The untranslated body, as supplied by the user,
    is the fifth element of the @(tsee defchoose) event.")
  (fifth (get-event fn wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defchoose-body ((fn (defchoose-namep fn wrld))
                        (wrld plist-worldp))
  :returns (body "A @(tsee pseudo-termp).")
  :mode :program
  :short (xdoc::topstring
          (xdoc::seetopic "term" "Translated")
          " body of a function introduced via @(tsee defchoose).")
  :long
  (xdoc::topstring
   (xdoc::p
    "The body @('body') is extracted from the constraining axiom of @('fn'),
     which has one of the following forms
     (see @('defchoose-constraint') in the ACL2 source code):")
   (xdoc::ul
    (xdoc::li
     "@('(implies body ...)'),
      if @(':strengthen') is @('nil')
      and @('fn') has one bound variable.")
    (xdoc::li
     "@('(if ... (implies body ...) nil)'),
      if @('strengthen') is @('nil')
      and @('fn') has more than one bound variable.")
    (xdoc::li
     "@('(if (implies body ...) ... nil)'),
      if @(':strengthen') is @('t')
      and @('fn') has one bound variable.")
    (xdoc::li
     "@('(if (if ... (implies body ...) nil) ... nil)'),
      if @('strengthen') is @('t')
      and @('fn') has more than one bound variable.")))
  (b* ((axiom (defchoosep fn wrld))
       (strengthen (defchoose-strengthen fn wrld))
       (bound-vars (defchoose-bound-vars fn wrld))
       (one-bound-var (= (len bound-vars) 1)))
    (if strengthen
        (if one-bound-var
            (second (second axiom))
          (second (third (second axiom))))
      (if one-bound-var
          (second axiom)
        (second (third axiom))))))
