; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../test-star")

(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (xdoc::set-default-parents atc-symbolic-execution-rules))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-boolean-equality-rules
  :short "Rules about boolean equalities."
  :long
  (xdoc::topstring
   (xdoc::p
    "We just have a fairly ad hoc rule here;
     since it is so ad hoc, it is not quite clear whether it is appropriate
     to put it into a more general library or not,
     so for now we leave it here.")
   (xdoc::p
    "The need for this rule arises in the modular theorems
     generated for the non-strict disjunctive operator @('||').
     In those theorems,
     a subgoal arises of the form @('(equal t <something>)'),
     where @('<something>') is a boolean.
     The rule below resolves this subgoal.
     Note that we cannot rewrite @('t') or a variable,
     and so we make the whole equality into the left side,
     with @('t') as the right side."))

  (defruled equal-to-t-when-holds-and-boolean
    (implies (and (booleanp b)
                  (test* b))
             (equal (equal t b) t))
    :enable test*))
