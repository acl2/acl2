; RISC-V Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "decoding-correct")

(include-book "../specification/execution")

(include-book "kestrel/apt/simplify" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ execution-executable
  :parents (executable)
  :short "Executable refinements of the execution functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the specification, the only functions that depend on @(tsee decode)
     are @(tsee step) and @(tsee stepn);
     the instruction semantic functions do not depend on decoding,
     because they operate on the instruction abstract syntax
     produced by decoding.
     Here we provide executable versions @(tsee stepx) and @(tsee stepnx)
     of @(tsee step) and @(tsee stepn),
     by propagating the refinement of @(tsee decode) to @(tsee decodex)
     via the @(tsee apt::simplify) transformation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stepx
  :short "Executable single-step execution function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained from @(tsee step) via @(tsee apt::simplify),
     passing @(tsee decode-is-decodex) to propagate it.
     The result is the same as @(tsee step),
     but with a call of @(tsee decodex) instead of @(tsee decode).
     The generated theorem that
     unconditionally rewrites @(tsee step) to @(tsee stepx)
     is @('step-to-stepx').")
   (xdoc::p
    "We manually propagate the fixing and state validity preservation theorems
     that accompany @(tsee step) to @('stepx')."))

  (apt::simplify step
    :new-name stepx
    :enable (decode-is-decodex)
    :thm-name step-is-stepx
    :thm-enable nil
    :untranslate :nice)

  (fty::deffixequiv stepx
    :args ((stat statp) (feat featp)))

  (defrule stat-validp-of-stepx
    (implies (stat-validp stat feat)
             (stat-validp (stepx stat feat) feat))
    :use stat-validp-of-step
    :disable stat-validp-of-step
    :enable step-is-stepx))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection stepx
  :short "Executable multi-step execution function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained from @(tsee stepn) via @(tsee apt::simplify),
     passing @(tsee step-is-stepx) to propagate it.
     The result is the same as @(tsee stepn),
     but with a call of @(tsee stepx) instead of @(tsee step).
     The generated theorem that
     unconditionally rewrites @(tsee stepn) to @(tsee stepnx)
     is @('stepn-to-stepnx').")
   (xdoc::p
    "We manually propagate the fixing and state validity preservation theorems
     that accompany @(tsee stepn) to @('stepnx')."))

  (apt::simplify stepn
    :new-name stepnx
    :enable (step-is-stepx)
    :thm-name stepn-is-stepnx
    :thm-enable nil
    :untranslate :nice)

  (fty::deffixequiv stepnx
    :args ((n natp) (stat statp) (feat featp))
    :hints (("Goal" :induct t :in-theory (enable stepnx nfix))))

  (defrule stat-validp-of-stepnx
    (implies (stat-validp stat feat)
             (stat-validp (stepnx n stat feat) feat))
    :use stat-validp-of-stepn
    :disable stat-validp-of-stepn
    :enable stepn-is-stepnx))
