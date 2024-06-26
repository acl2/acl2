; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-cpp)


(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

(include-book "../preprocess-file")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed
  (preprocess-file (filepath "stdbool.c")))

(acl2::must-succeed
  (acl2::must-eval-to-t
    (b* (((er (cons out -))
          (preprocess-file (filepath "stdbool.c") :out "stdbool.i")))
      (value (stringp out)))))

(acl2::must-succeed
  (preprocess-file (filepath "stdbool.i")))

(acl2::must-succeed
  (preprocess-file (filepath "stdbool.c") :out "stdbool.i" :save nil))

(acl2::must-fail
  (preprocess-file (filepath "nonexistent-file.c")))

(acl2::must-succeed
  (preprocess-file (filepath "../tests/stdint.c")))

(acl2::must-succeed
  (preprocess-files
    (mergesort (list (filepath "stdbool.c")
                     (filepath "stdint.c")))))

(acl2::must-succeed
  (acl2::must-eval-to
    (preprocess-files nil)
    (fileset nil)))
