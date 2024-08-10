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
               (file-at-path (filepath "simple.c") *files-simple*)))))

(output-files :const *renamed-files-simple*
              :process :write)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-files-simple/stdbool/stdint*
  (fileset
   (list (cons (filepath "simple-renamed.c")
               (file-at-path (filepath "simple.c")
                             *files-simple/stdbool/stdint*))
         (cons (filepath "stdbool-renamed.c")
               (file-at-path (filepath "stdbool.c")
                             *files-simple/stdbool/stdint*))
         (cons (filepath "stdint-renamed.c")
               (file-at-path (filepath "stdint.c")
                             *files-simple/stdbool/stdint*)))))

(output-files :const *renamed-files-simple/stdbool/stdint*
              :process :write)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Print and write.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Change paths, to avoid overwriting files.
(defconst *renamed-disamb-simple/stdbool*
  (transunit-ensemble
   (list (cons (filepath "simple-renamed-renamed.c")
               (transunit-at-path (filepath "simple.c")
                                  *disamb-simple/stdbool*))
         (cons (filepath "stdbool-renamed-renamed.c")
               (transunit-at-path (filepath "stdbool.c")
                                  *disamb-simple/stdbool*)))))

(output-files :const *renamed-disamb-simple/stdbool*
              :process :print)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(output-files :const *renamed-disamb-simple/stdbool*
              :process :print
              :const-files *renamed-files-simple/stdbool*)

(acl2::assert-equal
 (fileset-paths *renamed-files-simple/stdbool*)
 (list (filepath "simple-renamed-renamed.c")
       (filepath "stdbool-renamed-renamed.c")))
