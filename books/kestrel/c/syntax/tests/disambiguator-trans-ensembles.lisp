; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../input-files")
(include-book "../printer")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Disambiguator tests for translation ensembles.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(input-files :files '("included.c" "including.c")
             :base-dir "disamb-example1"
             :preprocess :internal
             :process :disambiguate
             :const *code1*)

(defconst *printed1*
  (print-fileset (code-ensemble->trans-units *code1*)
                 (default-priopt)
                 (ienv->dialect (code-ensemble->ienv *code1*))))

(acl2::assert-equal *printed1*
                    (fileset
                     (list (cons (filepath "included.c")
                                 (filedata
                                  (acl2::string=>nats
                                   "int x;
")))
                           (cons (filepath "including.c")
                                 (filedata
                                  (acl2::string=>nats
                                   "#include \"included.c\"

void f(int y) {
  x * y;
}
"))))))
