; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system/enhanced-utilities
  :parents (std/system)
  :short "System utilities with some enhanced features."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some built-in system utilities are not guard-verified;
     some are guard-verified but have weak guards,
     and also weak (or non-existent) return type theorems.
     Some system utilities in the @(csee std/system) library
     are similar in this respect
     (intentionally so, as they are meant to complement the built-in ones).
     Strengthening the guards and return type theorems of these utilities
     may require stronger @(see world) invariants,
     and thus quite a bit of work.
     Nonetheless, these utilities are adequate, in their current form,
     for code where proving properties of the code itself is not a focus
     (e.g. program-mode code).")
   (xdoc::p
    "For code where proving at least some type-like properties
     (particularly verifying guards and return types) is instead desired,
     the @(csee std/system) library provides ``enhanced'' versions
     of some of the aforementioned system utilities (built-in or not).
     These variants may have stronger guards,
     and often have stronger return type theorems:
     the latter are made possible via run-time checks
     that are expected to never fail.
     Because of the run-time checks,
     these variants are slower than the corresponding utilities
     with weaker guards and weaker (or no) return type theorems.
     These enhanced variants are named
     like the corresponding utilities,
     but with a @('+') at the end.")
   (xdoc::p
    "Besides the run-time checks for the return type theorems,
     some of these enhanced variants include
     additional run-time checks on their arguments.
     Making those checks part of the guards
     would make these utilities harder to use in practice,
     because it would be difficult to discharge
     their stronger guard obligations given the customary guards
     for the surrounding code.
     For instance, the customary @(tsee pseudo-termp) guard
     does not ensure that function symbols in terms
     satisfy @(tsee function-symbolp):
     so, if some enhanced utilities operating on named functions
     were to require the function symbol to satisfy @(tsee function-symbolp),
     the @(tsee pseudo-termp) guard
     would have to be replaced with something stronger.
     Instead, these enhanced utilities operating on named functions
     can check that @(tsee function-symbolp) at run time,
     helping to detect programming errors.")))
