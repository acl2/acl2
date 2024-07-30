; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../output-files")

(include-book "input-files") ; to get something to output

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Write.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-files-simple*
  (fileset
   (list (cons (filepath "simple-renamed.c")
               (omap::lookup (filepath "simple.c")
                             (fileset->unwrap *files-simple*))))))

(output-files :const *renamed-files-simple*
              :process :write)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-files-simple/stdbool/stdint*
  (b* ((map (fileset->unwrap *files-simple/stdbool/stdint*)))
    (fileset
     (list (cons (filepath "simple-renamed.c")
                 (omap::lookup (filepath "simple.c") map))
           (cons (filepath "stdbool-renamed.c")
                 (omap::lookup (filepath "stdbool.c") map))
           (cons (filepath "stdint-renamed.c")
                 (omap::lookup (filepath "stdint.c") map))))))

(output-files :const *renamed-files-simple/stdbool/stdint*
              :process :write)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Print and write.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-disamb-simple/stdbool*
  (b* ((map (transunit-ensemble->unwrap *disamb-simple/stdbool*)))
    (transunit-ensemble
     (list (cons (filepath "simple-renamed-renamed.c")
                 (omap::lookup (filepath "simple.c") map))
           (cons (filepath "stdbool-renamed-renamed.c")
                 (omap::lookup (filepath "stdbool.c") map))))))

(output-files :const *renamed-disamb-simple/stdbool*
              :process :print)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(output-files :const *renamed-disamb-simple/stdbool*
              :process :print
              :const-files *renamed-files-simple/stdbool*)

(acl2::assert-equal
 (omap::keys (fileset->unwrap *renamed-files-simple/stdbool*))
 (list (filepath "simple-renamed-renamed.c")
       (filepath "stdbool-renamed-renamed.c")))
