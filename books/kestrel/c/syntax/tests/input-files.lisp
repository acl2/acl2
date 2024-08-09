; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c" "stdint.c")
             :preprocess :auto
             :process :read
             :const *preproc-simple/stdbool/stdint-2*
             :const-files *files-simple/stdbool/stdint-2*)

(acl2::assert-equal *preproc-simple/stdbool/stdint-2*
                    *preproc-simple/stdbool/stdint*)

(acl2::assert-equal *files-simple/stdbool/stdint-2*
                    *files-simple/stdbool/stdint*)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :parse
             :const *parsed-simple-2*
             :const-files *files-simple-2*)

(acl2::assert-equal *parsed-simple-2*
                    *parsed-simple*)

(acl2::assert-equal *files-simple-2*
                    *files-simple*)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :parse
             :const *parsed-simple/stdbool-2*
             :const-files *files-simple/stdbool*)

(acl2::assert! (filesetp *files-simple/stdbool*))

(acl2::assert-equal *parsed-simple/stdbool-2*
                    *parsed-simple/stdbool*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :parse
             :const *parsed-simple/stdbool-3*
             :const-preproc *preproc-simple/stdbool*)

(acl2::assert! (filesetp *preproc-simple/stdbool*))

(acl2::assert-equal *parsed-simple/stdbool-3*
                    *parsed-simple/stdbool*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :parse
             :const *parsed-simple/stdbool-4*
             :const-files *files-simple/stdbool-2*
             :const-preproc *preproc-simple/stdbool-2*)

(acl2::assert-equal *parsed-simple/stdbool-4*
                    *parsed-simple/stdbool*)

(acl2::assert-equal *files-simple/stdbool-2*
                    *files-simple/stdbool*)

(acl2::assert-equal *preproc-simple/stdbool-2*
                    *preproc-simple/stdbool*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :disamb
             :const *disamb-simple*)

(acl2::assert! (transunit-ensemblep *disamb-simple*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c")
             :process :disamb
             :const *disamb-simple-2*
             :const-files *files-simple-3*
             :const-parsed *parsed-simple-3*)

(acl2::assert-equal *disamb-simple-2*
                    *disamb-simple*)

(acl2::assert-equal *files-simple-3*
                    *files-simple*)

(acl2::assert-equal *parsed-simple-3*
                    *parsed-simple*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read and preprocess and parse and disambiguate.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :disamb
             :const *disamb-simple/stdbool*)

(acl2::assert! (transunit-ensemblep *disamb-simple/stdbool*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files ("simple.c" "stdbool.c")
             ;; We exclude stdint.c because it has occurrences of #define
             ;; (not at the left margin) even after preprocessing.
             :preprocess :auto
             :process :disamb
             :const *disamb-simple/stdbool-2*
             :const-files *files-simple/stdbool-3*
             :const-preproc *preproc-simple/stdbool-3*
             :const-parsed *parsed-simple/stdbool-5*)

(acl2::assert-equal *disamb-simple/stdbool-2*
                    *disamb-simple/stdbool*)

(acl2::assert-equal *files-simple/stdbool-3*
                    *files-simple/stdbool*)

(acl2::assert-equal *preproc-simple/stdbool-3*
                    *preproc-simple/stdbool*)

(acl2::assert-equal *parsed-simple/stdbool-5*
                    *parsed-simple/stdbool*)
