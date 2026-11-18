; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
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
(defconst *renamed-ppext-disamb-simple/stdbool/stdint*
  (change-code-ensemble
   *ppext-disamb-simple/stdbool/stdint*
   :trans-units
   (make-trans-ensemble
    :units
    (list (cons (filepath "simple-renamed-renamed.c")
                (trans-unit-at-path (filepath "simple.c")
                                    (code-ensemble->trans-units
                                     *ppext-disamb-simple/stdbool/stdint*)))
          (cons (filepath "stdbool-renamed-renamed.c")
                (trans-unit-at-path (filepath "stdbool.c")
                                    (code-ensemble->trans-units
                                     *ppext-disamb-simple/stdbool/stdint*)))
          (cons (filepath "stdint-renamed-renamed.c")
                (trans-unit-at-path (filepath "stdint.c")
                                    (code-ensemble->trans-units
                                     *ppext-disamb-simple/stdbool/stdint*))))
    :resolved-includes nil
    :info nil)))

(output-files :const *renamed-ppext-disamb-simple/stdbool/stdint*)
