; Axe-specific rules
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "A")

(include-book "run-until-return")
(include-book "../axe-syntax-functions")
(include-book "../known-booleans")

;; These are all disabled, because they are for Axe, not the ACL2 rewriter.

(defthmd run-until-return-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (< call-stack-height 0))
           (equal (run-until-return-aux call-stack-height arm)
                  arm)))

(defthmd run-until-return-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (< call-stack-height 0)))
           (equal (run-until-return-aux call-stack-height arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-aux (update-call-stack-height call-stack-height arm) (step arm)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd run-until-return-or-reach-pc-aux-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (or (< call-stack-height 0)
                    (memberp (reg *pc* arm) ; (pc arm)
                             stop-pcs)))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  arm)))

(defthmd run-until-return-or-reach-pc-aux-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if arm dag-array)))
                (not (or (< call-stack-height 0)
                         (memberp (reg *pc* arm) ; (pc arm)
                                  stop-pcs))))
           (equal (run-until-return-or-reach-pc-aux call-stack-height stop-pcs arm)
                  ;; todo: decoding is done here twice (in update-call-stack-height and step):
                  (run-until-return-or-reach-pc-aux (update-call-stack-height call-stack-height arm) stop-pcs (step arm)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-known-boolean armp)
(add-known-boolean arm::conditionpassed) ; not sure if needed
