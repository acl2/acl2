; Standard Basic Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define good-valuep (x)
  :returns (yes/no booleanp)
  :parents (std/basic-extensions std/basic)
  :short "Check if a value is ``good''."
  :long
  (xdoc::topstring
   (xdoc::p
    "Check whether a value is either a good atom
     (i.e. a number, a character, a string, or a symbol)
     or a @(tsee cons) pair whose @(tsee car) and @(tsee cdr)
     are recursively good values.
     That is, check whether a value
     neiher is a bad atom
     nor contains (directly or indirectly) bad atoms.")
   (xdoc::p
    "These good values are the only ones that can be constructed in execution.
     However, in the ACL2 logic, there may be bad atoms,
     or @(tsee cons) pairs that contain, directly or indirectly, bad atoms.")
   (xdoc::p
    "Also see @(tsee good-atom-listp)."))
  (or (acl2-numberp x)
      (characterp x)
      (stringp x)
      (symbolp x)
      (and (consp x)
           (good-valuep (car x))
           (good-valuep (cdr x)))))
