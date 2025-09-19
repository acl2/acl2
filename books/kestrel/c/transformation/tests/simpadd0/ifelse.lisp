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

(include-book "../utilities")

; (depends-on "old/ifelse.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files '("ifelse.c")
                 :path "old"
                 :const *old-code*)

(simpadd0 *old-code* *new-code*)

(c$::output-files :const *new-code*
                  :path "new")

(assert-file-contents
 :file "new/ifelse.c"
 :content "int f(int x, int y) {
  if (x == y)
    return 1;
  else
    return 2;
}
")

(assert-highest-thm-has-exec-fun *new-code*)
