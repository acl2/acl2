; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

; cert_param: (uses-cpp)

(include-book "std/testing/must-eval-to-t" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

(include-book "../preprocess-file")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed
  (b* (((mv erp - - state)
        (preprocess-file (filepath "stdbool.c"))))
    (value (not erp))))

(acl2::must-succeed
  (acl2::must-eval-to-t
    (b* (((mv erp out - state)
          (preprocess-file (filepath "stdbool.c") :out "stdbool.i")))
      (value (and (not erp)
                  (stringp out))))))

(acl2::must-succeed
  (b* (((mv erp - - state)
        (preprocess-file (filepath "stdbool.i"))))
    (value (not erp))))

(acl2::must-succeed
  (b* (((mv erp - - state)
        (preprocess-file (filepath "stdbool.c") :out "stdbool.i" :save nil)))
    (value (not erp))))

(acl2::must-succeed
  (b* (((mv erp - - state)
        (preprocess-file (filepath "nonexistent-file.c"))))
    (value (and erp t))))

(acl2::must-succeed
  (b* (((mv erp - - state)
        (preprocess-file (filepath "../tests/stdint.c"))))
    (value (not erp))))

(acl2::must-succeed
  (b* (((mv erp - state)
        (preprocess-files
          (mergesort (list (filepath "stdbool.c")
                           (filepath "stdint.c"))))))
    (value (not erp))))

(acl2::must-succeed
  (b* (((mv erp fileset state)
        (preprocess-files nil)))
    (value (and (not erp)
                (equal fileset (fileset nil))))))

(acl2::must-succeed
  (b* (((mv erp - state)
        (preprocess-files
          (mergesort (list (filepath "stdbool.c")
                           (filepath "stdint.c")))
          :path "../tests")))
    (value (not erp))))
