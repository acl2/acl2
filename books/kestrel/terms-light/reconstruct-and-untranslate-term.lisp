; Compose reconstruct-lets-in-term with simple-untranslate-in-term
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "reconstruct-lets-in-term")
(include-book "simple-untranslate-in-term")

;; Apply RECONSTRUCT-LETS-IN-TERM followed by SIMPLE-UNTRANSLATE-IN-TERM.
;; The result is usually not a PSEUDO-TERMP, because RECONSTRUCT-LETS-IN-TERM
;; introduces LET / MV-LET / DECLARE surface forms.
(defund reconstruct-and-untranslate-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (simple-untranslate-in-term (reconstruct-lets-in-term term)))
