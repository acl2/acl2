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
