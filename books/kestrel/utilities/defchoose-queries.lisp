; DEFCHOOSE Queries
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities
; for recognizing functions introduced via DEFCHOOSE
; and for retrieving their DEFCHOOSE-specific constituents.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/system/world-queries" :dir :system)

(local (set-default-parents defchoose-queries))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defchoose-queries

  :parents (kestrel-utilities system-utilities defchoose)

  :short "Utilities to query @(tsee defchoose) functions."

  :long

  "<p>
  Since @(tsee defchoose) is a primitive event,
  functions introduced via @(tsee defchoose)
  can always be recognized precisely.
  Besides the non-@(tsee defchoose)-specific constituents
  (e.g. formal arguments),
  which can be queried
  with <see topic='@(url system-utilities)'>more general utilities</see>,
  these functions have @(tsee defchoose)-specific constituent,
  which can be queried with these @(tsee defchoose) query utilities.
  </p>")

(define defchoosep ((fn (function-namep fn wrld)) (wrld plist-worldp))
  ;; :returns (axiom pseudo-termp)
  :short
  "Check if the function @('fn') was introduced via @(tsee defchoose),
  returning the function's constraining axiom if the check succeeds."
  :long
  "<p>
  A function introduced via @(tsee defchoose) is recognizable
  by the presence of the @('defchoose-axiom') property,
  which is the axiom that constrains the function.
  </p>"
  (getpropc fn 'defchoose-axiom nil wrld)
  :guard-hints (("Goal" :in-theory (enable function-namep))))

(define defchoose-bound-vars ((fn (and (function-namep fn wrld)
                                       (defchoosep fn wrld)))
                              (wrld plist-worldp))
  :returns (bound-vars symbol-listp)
  :prepwork ((program))
  :short
  "Bound variables of the function @('fn') introduced via @(tsee defchoose)."
  :long
  "<p>
  The bound variables are in the third element of the @(tsee defchoose) event,
  which is either a single bound variable
  or a non-empty list of bound variables.
  </p>"
  (let* ((event (get-event fn wrld))
         (bound-var/bound-vars (third event)))
    (if (symbolp bound-var/bound-vars)
        (list bound-var/bound-vars)
      bound-var/bound-vars)))

(define defchoose-strengthen ((fn (and (function-namep fn wrld)
                                       (defchoosep fn wrld)))
                              (wrld plist-worldp))
  :returns (t/nil booleanp)
  :prepwork ((program))
  :short
  "Value of the @(':strengthen') option
  of the function @('fn') introduced via @(tsee defchoose)."
  :long
  "<p>
  If explicitly supplied, the value of the @(':strengthen') option
  is the last element of the @(tsee defchoose) event,
  which consists of seven element in this case.
  If not explicitly supplied,
  the value of the @(':strengthen') option is @('nil'),
  and the @(tsee defchoose) event consists of five elements only.
  </p>"
  (let ((event (get-event fn wrld)))
    (if (eql (len event) 5)
        nil
      (car (last event)))))

(define defchoose-untrans-body ((fn (and (function-namep fn wrld)
                                         (defchoosep fn wrld)))
                                (wrld plist-worldp))
  :prepwork ((program))
  :short
  "Body of the function @('fn') introduced via @(tsee defchoose),
  in <see topic='@(url term)'>untranslated form</see>."
  :long
  "<p>
  The untranslated body, as supplied by the user,
  is the fifth element of the @(tsee defchoose) event.
  </p>"
  (fifth (get-event fn wrld)))

(define defchoose-body ((fn (and (function-namep fn wrld)
                                 (defchoosep fn wrld)))
                        (wrld plist-worldp))
  :returns (body pseudo-termp)
  :prepwork ((program))
  :short
  "Body of the function @('fn') introduced via @(tsee defchoose),
  in <see topic='@(url term)'>translated form</see>."
  :long
  "<p>
  The body @('body') is extracted from the constraining axiom of @('fn'),
  which has one of the following forms
  (see @('defchoose-constraint') in the ACL2 source code):
  </p>
  <ul>
    <li>
    @('(implies body ...)'),
    if @(':strengthen') is @('nil')
    and @('fn') has one bound variable.
    </li>
    <li>
    @('(if ... (implies body ...) nil)'),
    if @('strengthen') is @('nil')
    and @('fn') has more than one bound variable.
    </li>
    <li>
    @('(if (implies body ...) ... nil)'),
    if @(':strengthen') is @('t')
    and @('fn') has one bound variable.
    </li>
    <li>
    @('(if (if ... (implies body ...) nil) ... nil)'),
    if @('strengthen') is @('t')
    and @('fn') has more than one bound variable.
    </li>
  </ul>"
  (b* ((axiom (defchoosep fn wrld))
       (strengthen (defchoose-strengthen fn wrld))
       (bound-vars (defchoose-bound-vars fn wrld))
       (one-bound-var (eql (len bound-vars) 1)))
    (if strengthen
        (if one-bound-var
            (second (second axiom))
          (second (third (second axiom))))
      (if one-bound-var
          (second axiom)
        (second (third axiom))))))
