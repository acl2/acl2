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

(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-let-designations
  :parents (atc-implementation)
  :short "Designations of @(tsee let) representations for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ACL2's @(tsee let) is used to represent three different things in C:")
   (xdoc::ul
    (xdoc::li
     "A local variable declaration with an initializer.")
    (xdoc::li
     "An assignment of an expression to a local variable.")
    (xdoc::li
     "A transformation of a local variable via statements."))
   (xdoc::p
    "The third is related to @(tsee mv-let) being used to represent
     a transformation of two or more local variables via statements;
     @(tsee mv-let) never represents local variable declarations or assignments.
     Note that an assignment to a local variable
     is a transformation of the local variables via an expression,
     as opposed to a transformation via statements.")
   (xdoc::p
    "Since each of these three different uses
     is only allowed under suitable conditions,
     ATC could (and past version of ATC did) distinguish the three uses
     based on the satisfaction of such conditions.
     However, in the interest of not only keeping ATC simpler
     but also encouraging the user to explicate their intention,
     ATC requires these three uses to be explicitly indicated.
     Since we cannot really define three different versions of @(tsee let)
     (ATC operates on translated terms, not untranslated ones),
     our approach is to add a wrapper to the term bound to the variable.
     The wrapper is the identity function,
     but its presence provides the needed indication to ATC:")
   (xdoc::codeblock
    "(let ((var (<wrapper> term))) body)")
   (xdoc::p
    "We provide
     a wrapper to indicate a declaration,
     a wrapper to indicate an assignment,
     and no wrapper to indicate a transformation via staetements.
     The no-wrapper indication for the latter case matches @(tsee mv-let),
     which also transforms variables via statements and also has no wrappers.")
   (xdoc::p
    "We remark that an external (APT) transformation
     could automatically add the needed wrappers
     based on the conditions under which a @(tsee let) occurs.
     Thus, our approach does not forgo automation,
     but rather modularizes the problem into simpler pieces."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declar (x)
  :short "Wrapper to indicate a C local variable declaration."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assign (x)
  :short "Wrapper to indicate a C local variable assignment."
  :long
  (xdoc::topstring-p
   "See @(tsee atc-let-designations).")
  x)
