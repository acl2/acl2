; C Library
;
; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

(include-book "../../../syntax/input-files")

(include-book "../../utilities/call-graph")
(include-book "../../utilities/qualified-ident")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *ienv-gcc*
  (c$::ienv-default :dialect (c::make-dialect :std (c::standard-c17)
                                              :gcc t)))

(c$::input-files :files '("a.c" "b.c" "calls.c" "recursion.c")
                 :const *code*
                 :ienv *ienv-gcc*)

(defconst *ensemble*
  (code-ensemble->trans-units *code*))

(defconst *call-graph*
  (trans-ensemble-call-graph *ensemble*))

(defun uid-of (qual-ident)
  (declare (xargs :mode :program))
  (mv-let (erp uid)
    (resolve-qualified-ident qual-ident *ensemble*)
    (if erp
        (er hard? 'uid-of "~@0" erp)
      uid)))

(defun external-uid (name)
  (declare (xargs :mode :program))
  (uid-of (external-ident (ident name))))

(defun internal-uid (file name)
  (declare (xargs :mode :program))
  (uid-of (qualified-ident (filepath file) (ident name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Calls across translation units resolve to the same node. Static functions
;; with the same name in different translation units are distinct nodes.

(acl2::assert! (not (equal (internal-uid "a.c" "helper")
                           (internal-uid "b.c" "helper"))))

(acl2::assert-equal
  (graph::successors (external-uid "entry") *call-graph*)
  (treeset::set (internal-uid "a.c" "helper")
                (external-uid "shared")))

(acl2::assert-equal
  (graph::successors (external-uid "shared") *call-graph*)
  (treeset::set (internal-uid "b.c" "helper")))

;; A defined function which calls nothing has no successors.

(acl2::assert-equal
  (graph::successors (external-uid "leaf") *call-graph*)
  (treeset::empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parentheses, & and * around a function name still call that function.

(acl2::assert-equal
  (graph::successors (external-uid "forms") *call-graph*)
  (treeset::set (external-uid "leaf")))

;; Calls through a pointer are not resolved, including through a global
;; pointer, whose unique identifier has the same form as a function's, and
;; through a parameter which shadows a function of the same name.

(acl2::assert-equal
  (graph::successors (external-uid "through_pointer") *call-graph*)
  (treeset::set nil))

(acl2::assert-equal
  (graph::successors (external-uid "through_global_pointer") *call-graph*)
  (treeset::set nil))

(acl2::assert! (not (graph::node-in (external-uid "global_fp") *call-graph*)))

(acl2::assert-equal
  (graph::successors (external-uid "shadowed") *call-graph*)
  (treeset::set nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Functions without a definition, including built-ins, have an edge to nil.

(acl2::assert-equal
  (graph::successors (external-uid "calls_undefined") *call-graph*)
  (treeset::set (external-uid "undefined")))

(acl2::assert-equal
  (graph::successors (external-uid "undefined") *call-graph*)
  (treeset::set nil))

(acl2::assert-equal
  (graph::successors (c$::uid-external (ident "__builtin_expect"))
                     *call-graph*)
  (treeset::set nil))

;; A built-in which the validator does not know is still a direct call.

(acl2::assert-equal
  (graph::successors (external-uid "calls_unknown_builtin") *call-graph*)
  (treeset::set (c$::uid-external (ident "__builtin_parity"))))

;; Assembler statements may call anything.

(acl2::assert-equal
  (graph::successors (external-uid "with_asm") *call-graph*)
  (treeset::set nil))

;; Size expressions of variably modified parameters are evaluated on entry.

(acl2::assert-equal
  (graph::successors (external-uid "vla_param") *call-graph*)
  (treeset::set (external-uid "size")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
  (cg-calls-3p (external-uid "fact") (external-uid "fact") *call-graph*)
  t)

(acl2::assert-equal
  (cg-calls-3p (external-uid "odd") (external-uid "odd") *call-graph*)
  nil)

;; A function without a definition may call anything.

(acl2::assert-equal
  (cg-calls-3p (external-uid "declared_only")
               (external-uid "fact")
               *call-graph*)
  :unknown)

(acl2::assert-equal
  (cg-calls+-3p (external-uid "not_recursive")
                (external-uid "fact")
                *call-graph*)
  t)

(acl2::assert-equal
  (cg-recursive-3p (external-uid "odd") *call-graph*)
  t)

(acl2::assert-equal
  (cg-recursive-3p (external-uid "not_recursive") *call-graph*)
  nil)

(acl2::assert-equal
  (cg-recursive-3p (external-uid "callback") *call-graph*)
  :unknown)
