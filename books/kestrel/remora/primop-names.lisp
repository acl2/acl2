; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "kestrel/fty/string-set" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The names are sorted once, when the constant is defined, rather than at
; each call of PRIMOP-NAMES.

(defconst *primop-names*
  (set::mergesort
   '("+"
     "-"
     "*"
     "/"
     "^"
     "mod"
     "max"
     "min"
     "bit-and"
     "bit-or"
     "bit-xor"
     "shl"
     "shr"
     "bit-not"
     "popc"
     "=="
     "!="
     "<"
     ">"
     "<="
     ">="
     "i->f"
     "i->bool"
     "f.+"
     "f.-"
     "f.*"
     "f./"
     "f.^"
     "f.max"
     "f.min"
     "sqrt"
     "f.sqrt"
     "f.=="
     "f.!="
     "f.<"
     "f.>"
     "f.<="
     "f.>="
     "truncate"
     "round"
     "ceiling"
     "floor"
     "not"
     "and"
     "or"
     "bool.=="
     "bool.!="
     "bool->i"
     "bool->f"
     "head"
     "tail"
     "length"
     "append"
     "reverse"
     "index"
     "index2d"
     "sum"
     "reshape"
     "flatten"
     "transpose2d"
     "iota/static"
     "reduce"
     "fold"
     "reify-dim"
     "reify-shape"
     "iota"
     "trace"
     "undefined")))

(define primop-names ()
  :parents (abstract-syntax)
  :returns (names string-setp)
  :short "The surface names of the primitive operations, as a set."
  :long
  (xdoc::topstring
   (xdoc::p
    "The primitive operations are denoted by variables with these names,
     which are implicitly in scope: they are the keys of the initial static
     and dynamic environments (see @(tsee primop-types) and
     @(tsee primop-values)), and the theorem
     @('keys-of-primop-values') in the validation of the uniquification
     ties this syntactic list to the dynamic one.")
   (xdoc::p
    "The list is needed at the syntactic level by
     @(tsee expr-uniquify-names), whose generated binder names must avoid
     these names as well as the names occurring in the expression: a
     binder freshened to a primitive operation's name would shadow that
     operation in the (uniquified) scope of the binder, although the
     original scope does not, which the validation of the uniquification
     against evaluation could not tolerate."))
  *primop-names*)
