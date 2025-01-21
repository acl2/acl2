; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-cpp)

(include-book "../input-files")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :const *files-simple*
             :process :read)

(acl2::assert! (filesetp *files-simple*))

(acl2::assert-equal
 *files-simple*
 (fileset (list (cons (filepath "simple.c")
                      (filedata
                       (acl2::string=>nats
                        "int main(void) {
  return 0;
}
"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c" "stdint.c")
             :const *files-simple/stdbool/stdint*
             :process :read)

(acl2::assert! (filesetp *files-simple/stdbool/stdint*))

(acl2::assert-equal
 *files-simple/stdbool/stdint*
 (fileset (list (cons (filepath "simple.c")
                      (filedata
                       (acl2::string=>nats
                        "int main(void) {
  return 0;
}
")))
                (cons (filepath "stdbool.c")
                      (filedata
                       (acl2::string=>nats
                        "#include <stdbool.h>

int main(void) {
  return (int)false;
}
")))
                (cons (filepath "stdint.c")
                      (filedata
                       (acl2::string=>nats
                        "#include <stdint.h>

int main(void) {
  uint32_t x = 0;
  return 0;
}
"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and preprocess.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :read
             :const *preproc-simple/stdbool/stdint*)

(acl2::assert! (filesetp *preproc-simple/stdbool/stdint*))

(acl2::assert-equal
 (fileset-paths *preproc-simple/stdbool/stdint*)
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c")
                       (filepath "stdint.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :parse
             :const *parsed-simple*)

(acl2::assert! (transunit-ensemblep *parsed-simple*))

(acl2::assert-equal
 (transunit-ensemble-paths *parsed-simple*)
 (set::mergesort (list (filepath "simple.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and preprocess and parse.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :parse
             :const *parsed-simple/stdbool*)

(acl2::assert! (transunit-ensemblep *parsed-simple/stdbool*))

(acl2::assert-equal
 (transunit-ensemble-paths *parsed-simple/stdbool*)
 (set::mergesort (list (filepath "simple.c")
                       (filepath "stdbool.c"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :disambiguate
             :const *disamb-simple*)

(acl2::assert! (transunit-ensemblep *disamb-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and preprocess and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :disambiguate
             :const *disamb-simple/stdbool*)

(acl2::assert! (transunit-ensemblep *disamb-simple/stdbool*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :validate
             :const *valid-simple*)

(acl2::assert! (transunit-ensemblep *valid-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and preprocess and parse and disambiguate and validate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :validate
             :const *valid-simple/stdbool*)

(acl2::assert! (transunit-ensemblep *valid-simple/stdbool*))
