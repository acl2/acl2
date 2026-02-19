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
  (code-ensemble
   (c$::make-transunit-ensemble
     :units
     (list (cons (filepath "simple-renamed-renamed.c")
                 (transunit-at-path (filepath "simple.c")
                                    (code-ensemble->transunits
                                      *ppext-disamb-simple/stdbool/stdint*)))
           (cons (filepath "stdbool-renamed-renamed.c")
                 (transunit-at-path (filepath "stdbool.c")
                                    (code-ensemble->transunits
                                      *ppext-disamb-simple/stdbool/stdint*)))
           (cons (filepath "stdint-renamed-renamed.c")
                 (transunit-at-path (filepath "stdint.c")
                                    (code-ensemble->transunits
                                      *ppext-disamb-simple/stdbool/stdint*)))))
   (code-ensemble->ienv *ppext-disamb-simple/stdbool/stdint*)))

(output-files :const *renamed-ppext-disamb-simple/stdbool/stdint*)
