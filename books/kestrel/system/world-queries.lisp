; World Queries
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains utilities for querying ACL2 worlds
; that complement the world query utilities in the ACL2 source code.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/basic/top" :dir :system)
(include-book "std/util/top" :dir :system)

(local (set-default-parents world-queries))

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc world-queries
  :parents (kestrel-system-utilities system-utilities)
  :short "Utilities to query <see topic='@(url world)'>worlds</see>."
  :long
  "<p>
  These complement the world query utilities
  in the <see topic='@(url system-utilities)'>built-in system utilities</see>.
  </p>")

(define theorem-symbolp ((sym symbolp) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the symbol @('sym') names a theorem,
  i.e. it has a @('theorem') property."
  (not (eq t (getpropc sym 'theorem t w))))

(define function-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a function."
  (and (symbolp x) (function-symbolp x w)))

(define theorem-namep (x (w plist-worldp))
  :returns (yes/no booleanp)
  :short "True iff @('x') is a symbol that names a theorem."
  (and (symbolp x) (theorem-symbolp x w)))

(define definedp ((fun (function-namep fun w)) (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the function @('fun') is defined,
  i.e. it has an @('unnormalized-body') property."
  (not (eq t (getpropc fun 'unnormalized-body t w))))

(define guard-verifiedp ((fun/thm (or (function-namep fun/thm w)
                                      (theorem-namep fun/thm w)))
                         (w plist-worldp))
  :returns (yes/no booleanp)
  :short
  "True iff the function or theorem @('fun/thm') is @(tsee guard)-verified."
  (eq (symbol-class fun/thm w) :common-lisp-compliant))

(define non-executablep ((fun (and (function-namep fun w)
                                   (definedp fun w)))
                         (w plist-worldp))
  :returns (result (member result '(t nil :program)))
  :short "The @(tsee non-executable) status of the defined function @('fun')."
  (getpropc fun 'non-executablep nil w))

(define measure ((fun (and (function-namep fun w)
                           (logicalp fun w)
                           (recursivep fun w)))
                 (w plist-worldp))
  :returns (measure pseudo-termp)
  :short "Measure expression of a logic-mode recursive function."
  :long "<p>See @(see xargs) for a discussion of the @(':measure') keyword.</p>"
  (access justification (getpropc fun 'justification nil w) :measure))

(define well-founded-relation ((fun (and (function-namep fun w)
                                         (logicalp fun w)
                                         (recursivep fun w)))
                               (w plist-worldp))
  :returns (well-founded-relation symbolp)
  :short "Well-founded relation of a logic-mode recursive function."
  :long
  "<p>See @(see well-founded-relation-rule)
  for a discussion of well-founded relations in ACL2,
  including the @(':well-founded-relation') rule class.</p>"
  (access justification (getpropc fun 'justification nil w) :rel))

(define fundef-enabledp ((fun (function-namep fun (w state))) state)
  :returns (yes/no booleanp)
  :short "True iff the definition of the function @('fun') is enabled."
  (not (member-equal `(:definition ,fun) (disabledp fun))))

(define rune-enabledp ((rune (runep rune (w state))) state)
  :returns (yes/no booleanp)
  :short "True iff the @(see rune) @('rune') is enabled."
  (not (member-equal rune (disabledp (cadr rune)))))
