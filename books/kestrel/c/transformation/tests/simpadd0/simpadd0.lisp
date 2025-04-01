; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../../simpadd0")

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("file1.c")
                 :path "old"
                 :const *old-code1*)

(simpadd0 *old-code1* *new-code1*)

(c$::output-files :const *new-code1*
                  :path "new")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("file2.c")
                 :path "old"
                 :const *old-code2*)

(simpadd0 *old-code2* *new-code2*)

(c$::output-files :const *new-code2*
                  :path "new")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("file3.c")
                 :path "old"
                 :const *old-code3*)

(simpadd0 *old-code3* *new-code3*)

(c$::output-files :const *new-code3*
                  :path "new")
