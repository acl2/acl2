; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../print-files")

(include-book "parse-files") ; to obtain translation unit ensembles

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(print-files :const-fileset *stdbool-printed*
             :const-transunits *stdbool-ast*)

(acl2::assert-equal
 (acl2::nats=>string
  (filedata->unwrap
   (omap::lookup (filepath "stdbool.c")
                 (fileset->unwrap *stdbool-printed*))))
 "int main(void) {
  return (int) 0;
}")
