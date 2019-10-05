; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/logic-friendly
  :parents (std/system)
  :short "System utilities that are logic-friendly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some built-in system utilities are in logic mode and guard-verified
     but have weak guards and weak (or non-existent) return type theorems.
     Some system utilities in the Std/system library
     are similar in this respect.
     Strengthening the guards and return type theorems of these utilities
     may require stronger @(see world) invariants,
     and thus quite a bit of work.
     Nonetheless, these utilities are adequate, in their current form,
     for code where proving properties of the code itself is not a focus
     (e.g. program-mode code).")
   (xdoc::p
    "For code where proving at least some type-like properties
     (particularly guard verification and return types)
     is instead desired,
     the Std/system library provides variants
     of some of the aforementioned system utilities (built-in or not).
     These variants normally have stronger guards
     as well as stronger return type theorems:
     the latter are made possible via run-time checks
     that are expected to never fail.
     In this sense, these variants are logic-friendly.
     Because of the run-time checks,
     these variants are slower than the corresponding utilities
     with weaker guards and weaker (or no) return type theorems.
     The logic-friendly variants are named
     the same as the corresponding utilities,
     but with a @('+') at the end.")))
