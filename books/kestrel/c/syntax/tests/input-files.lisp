; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-gcc-c17)

(include-book "../input-files")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :parse
             :const *parsed-simple*)

(acl2::assert! (code-ensemblep *parsed-simple*))

(acl2::assert-equal
 (transunit-ensemble-paths (code-ensemble->transunits *parsed-simple*))
 (set::mergesort (list (filepath "simple.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :parse
             :const *parsed-simple/stdbool*)

(acl2::assert! (code-ensemblep *parsed-simple/stdbool*))

(acl2::assert-equal
 (transunit-ensemble-paths (code-ensemble->transunits *parsed-simple/stdbool*))
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :disambiguate
             :const *disamb-simple*)

(acl2::assert! (code-ensemblep *disamb-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :disambiguate
             :const *disamb-simple/stdbool*)

(acl2::assert! (code-ensemblep *disamb-simple/stdbool*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :validate
             :const *valid-simple*)

(acl2::assert! (code-ensemblep *valid-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess and parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :validate
             :const *valid-simple/stdbool*)

(acl2::assert! (code-ensemblep *valid-simple/stdbool*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in parsing

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files ("failparse.c")
               :const *failparse*))

;; Ensures the error is in parsing, not a later step
(must-fail
  (input-files :files ("failparse.c")
               :process :parse
               :const *failparse*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in disambiguating

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files ("faildimb.c")
               :const *faildimb*))

;; Ensures no error if we only parse, not disambiguate
(input-files :files ("faildimb.c")
             :process :parse
             :const *faildimb-parse-only*)

;; Ensures the error is not in validation (together with the above test, this
;; ensures the error is in disambiguation)
(must-fail
  (input-files :files ("faildimb.c")
               :process :disambiguate
               :const *faildimb*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in validation

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files ("failvalidate.c")
               :process :validate ; the default
               :const *failvalidate*))

;; Ensures no error if we only parse+disambiguate, not validate, so the error
;; must be in validation
(input-files :files ("failvalidate.c")
             :process :disambiguate
             :const *failvalidate-parse-and-dimb-only*)
