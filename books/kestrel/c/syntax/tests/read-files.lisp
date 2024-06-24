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

(include-book "../read-files")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Without preprocessing.

;;;;;;;;;;;;;;;;;;;;

(read-files :const *stdbool*
            :files ("stdbool.c"))

(read-files :const *stdint*
            :files ("stdint.c"))

(read-files :const *stdbool-stdint*
            :files ("stdbool.c"
                    "stdint.c"))

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdbool.c")
                                    (fileset->unwrap *stdbool-stdint*))))
 "#include <stdbool.h>

int main(void) {
  return (int)false;
}
")

;;;;;;;;;;;;;;;;;;;;

(acl2::assert-equal
 (acl2::nats=>string (filedata->unwrap
                      (omap::lookup (filepath "stdint.c")
                                    (fileset->unwrap *stdbool-stdint*))))
 "#include <stdint.h>

int main(void) {
  uint32_t x = 0;
  return 0;
}
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With preprocessing.

;;;;;;;;;;;;;;;;;;;;

(read-files :const *stdbool-pp*
            :files ("stdbool.c")
            :preprocessor :auto)

(read-files :const *stdint-pp*
            :files ("stdint.c")
            :preprocessor :auto)

(read-files :const *stdbool-stdint-pp*
            :files ("stdbool.c"
                    "stdint.c")
            :preprocessor :auto)
