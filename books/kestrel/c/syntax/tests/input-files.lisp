; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-gcc-c17)

(include-book "../input-files")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse (without preprocessing).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c")
             :process :parse
             :const *parsed-simple*)

(acl2::assert! (code-ensemblep *parsed-simple*))

(acl2::assert-equal
 (transunit-ensemble-paths (code-ensemble->transunits *parsed-simple*))
 (set::mergesort (list (filepath "simple.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess externally and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c")
             :preprocess :auto
             :process :parse
             :const *ppext-parsed-simple*)

(acl2::assert! (code-ensemblep *ppext-parsed-simple*))

(acl2::assert-equal
 (transunit-ensemble-paths (code-ensemble->transunits *ppext-parsed-simple*))
 (set::mergesort (list (filepath "simple.c"))))

(acl2::assert-equal *ppext-parsed-simple*
                    *parsed-simple*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :parse
             :const *ppext-parsed-simple/stdbool/stdint*)

(acl2::assert! (code-ensemblep *ppext-parsed-simple/stdbool/stdint*))

(acl2::assert-equal
 (transunit-ensemble-paths
  (code-ensemble->transunits *ppext-parsed-simple/stdbool/stdint*))
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c")
                       (filepath "stdint.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess externally with list arguments and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :parse
             :preprocess-args '("-E" "-std=c17")
             :const *ppextlist-parsed-simple/stdbool/stdint*)

(acl2::assert! (code-ensemblep *ppextlist-parsed-simple/stdbool/stdint*))

(acl2::assert-equal
 (transunit-ensemble-paths
   (code-ensemble->transunits *ppextlist-parsed-simple/stdbool/stdint*))
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c")
                       (filepath "stdint.c"))))

(acl2::assert-equal *ppextlist-parsed-simple/stdbool/stdint*
                    *ppext-parsed-simple/stdbool/stdint*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess externally with omap arguments and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *preprocess-args-simple/stdbool/stdint*
  (omap::update "simple.c"
                (list "-P" "-std=c17")
                (omap::update "stdbool.c"
                              (list "-std=c17" "-P")
                              (omap::update "stdint.c"
                                            (list "-std=c17" "-P")
                                            nil))))

(input-files :files '("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :parse
             :preprocess-args *preprocess-args-simple/stdbool/stdint*
             :const *ppextomap-parsed-simple/stdbool/stdint*)

(acl2::assert! (code-ensemblep *ppextomap-parsed-simple/stdbool/stdint*))

(acl2::assert-equal
 (transunit-ensemble-paths
   (code-ensemble->transunits *ppextomap-parsed-simple/stdbool/stdint*))
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c")
                       (filepath "stdint.c"))))

(acl2::assert-equal *ppextlist-parsed-simple/stdbool/stdint*
                    *ppext-parsed-simple/stdbool/stdint*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *preprocess-args-macro-tests*
  (omap::update "macro_test1.c"
                (list "-DMY_MACRO=0")
                (omap::update "macro_test2.c"
                              (list "-DMY_MACRO=1")
                              nil)))

(input-files :files '("macro_test1.c" "macro_test2.c")
             :preprocess :auto
             :preprocess-args *preprocess-args-macro-tests*
             :const *macro-tests*)

(acl2::assert! (code-ensemblep *macro-tests*))

(acl2::assert-equal
 (transunit-ensemble-paths
   (code-ensemble->transunits *macro-tests*))
 (set::mergesort (list (filepath "macro_test1.c")
                       (filepath "macro_test2.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test with GCC extensions.
(input-files :files '("macro_test1.c" "macro_test2.c")
             :preprocess :auto
             :preprocess-args *preprocess-args-macro-tests*
             :ienv (ienv-default :extensions :gcc)
             :const *macro-tests2*)

(acl2::assert! (code-ensemblep *macro-tests2*))

(acl2::assert-equal
 (transunit-ensemble-paths
   (code-ensemble->transunits *macro-tests2*))
 (set::mergesort (list (filepath "macro_test1.c")
                       (filepath "macro_test2.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess internally and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c")
             :preprocess :internal
             :process :parse
             :const *ppint-parsed-simple*)

(acl2::assert! (code-ensemblep *ppint-parsed-simple*))

(acl2::assert-equal
 (transunit-ensemble-paths (code-ensemble->transunits *ppint-parsed-simple*))
 (set::mergesort (list (filepath "simple.c"))))

(acl2::assert-equal *ppint-parsed-simple*
                    *parsed-simple*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse and disambiguate (without preprocessing).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c")
             :process :disambiguate
             :const *disamb-simple*)

(acl2::assert! (code-ensemblep *disamb-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess externally and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :disambiguate
             ;; We need GCC (or Clang) extensions because
             ;; stdint.h brings in __buildin_va_list.
             :ienv (ienv-default :extensions :gcc)
             :const *ppext-disamb-simple/stdbool/stdint*)

(acl2::assert! (code-ensemblep *ppext-disamb-simple/stdbool/stdint*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c")
             :process :validate
             :const *valid-simple*)

(acl2::assert! (code-ensemblep *valid-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Preprocess externally and parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :validate
             ;; We need GCC (or Clang) extensions because
             ;; stdint.h brings in __buildin_va_list.
             :ienv (ienv-default :extensions :gcc)
             :const *valid-simple/stdbool/stdint*)

(acl2::assert! (code-ensemblep *valid-simple/stdbool/stdint*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in parsing.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files '("failparse.c")
               :const *failparse*))

;; Ensures the error is in parsing, not a later step
(must-fail
  (input-files :files '("failparse.c")
               :process :parse
               :const *failparse*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in disambiguation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files '("faildimb.c")
               :const *faildimb*))

;; Ensures no error if we only parse, not disambiguate
(input-files :files '("faildimb.c")
             :process :parse
             :const *faildimb-parse-only*)

;; Ensures the error is not in validation (together with the above test, this
;; ensures the error is in disambiguation)
(must-fail
  (input-files :files '("faildimb.c")
               :process :disambiguate
               :const *faildimb*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error in validation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
  (input-files :files '("failvalidate.c")
               :process :validate ; the default
               :const *failvalidate*))

;; Ensures no error if we only parse+disambiguate, not validate, so the error
;; must be in validation
(input-files :files '("failvalidate.c")
             :process :disambiguate
             :const *failvalidate-parse-and-dimb-only*)
