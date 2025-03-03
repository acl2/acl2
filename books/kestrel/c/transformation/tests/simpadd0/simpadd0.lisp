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
                 :const *old-code1*)

(simpadd0 *old-code1* *new-code1* :proofs t)

(c$::output-files :const *new-code1*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("file2.c")
                 :const *old-code2*)

(simpadd0 *old-code2* *new-code2* :proofs nil)

(c$::output-files :const *new-code2*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("file3.c")
                 :const *old-code3*)

(simpadd0 *old-code3* *new-code3* :proofs nil)

(c$::output-files :const *new-code3*)
