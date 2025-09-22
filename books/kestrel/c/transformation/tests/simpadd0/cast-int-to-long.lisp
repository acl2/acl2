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

; (depends-on "old/cast_int_to_long.c")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files ("cast_int_to_long.c")
                 :path "old"
                 :const *old-code*)

(simpadd0 :const-old *old-code*
          :const-new *new-code*)

(c$::output-files :const *new-code*
                  :path "new")

(assert-file-contents
 :file "new/cast_int_to_long.c"
 :content "long cast_int_to_long(int x) {
  return (long) x;
}
")

(assert-highest-thm-has-exec-fun *new-code*)
