; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../write-files")

(include-book "print-files") ; to obtain file sets

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths in file set, to avoid overwriting original files.
(defconst *stdbool-printed-diff-path*
  (fileset
   (omap::update (filepath "stdbool-printed.c")
                 (omap::lookup (filepath "stdbool.c")
                               (fileset->unwrap *stdbool-printed*))
                 nil)))

(write-files :const *stdbool-printed-diff-path*)
