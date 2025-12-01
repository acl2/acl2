; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../output-files")

(include-book "input-files") ; to get something to output

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Print and write.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-disamb-simple/stdbool*
  (code-ensemble
   (transunit-ensemble
    (list (cons (filepath "simple-renamed-renamed.c")
                (transunit-at-path (filepath "simple.c")
                                   (code-ensemble->transunits
                                    *disamb-simple/stdbool*)))
          (cons (filepath "stdbool-renamed-renamed.c")
                (transunit-at-path (filepath "stdbool.c")
                                   (code-ensemble->transunits
                                    *disamb-simple/stdbool*)))))
   (code-ensemble->ienv *disamb-simple/stdbool*)))

(output-files :const *renamed-disamb-simple/stdbool*)
