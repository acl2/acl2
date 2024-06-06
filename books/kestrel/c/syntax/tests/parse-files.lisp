; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parse-files")

(include-book "read-files") ; to obtain preprocessed files

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(parse-files :const-transunits *stdbool-ast*
             :const-fileset *stdbool-pp*)

; This fails because there are still #define occurrences in *stdint-pp*.
;; (parse-files :const-transunits *stdint-ast*
;;              :const-fileset *stdint-pp*)
