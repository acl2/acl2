; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../print-and-write-files")

(include-book "input-files") ; to obtain translation unit ensembles

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths in file set, to avoid overwriting original files.
(defconst *stdbool-ast-diff-path*
  (transunit-ensemble
   (omap::update (filepath "stdbool-printed.c")
                 (omap::lookup (filepath "stdbool.c")
                               (transunit-ensemble->unwrap *parsed-simple/stdbool*))
                 nil)))

(print-and-write-files :const *stdbool-ast-diff-path*)
