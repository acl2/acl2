; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../simpadd0")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *old-filedata*
  (filedata
   (acl2::string=>nats
    "int main() {
  int x = 5;
  return x + 0;
}
")))

(defconst *old-fileset*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata*
                 nil)))

(defconst *old-transunits*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset* nil)))
    (if erp
        (cw "~@0" erp)
      transunits)))

(defconst *new-transunits*
  (simpadd0-transunit-ensemble *old-transunits*))

(defconst *new-fileset*
  (c$::print-fileset *new-transunits* (c$::default-priopt)))

(defconst *new-filepath*
  (filepath "file.simpadd0.c"))

(defconst *new-filedata*
  (omap::lookup *new-filepath*
                (fileset->unwrap *new-fileset*)))

(assert-event
 (equal
  (acl2::nats=>string
   (filedata->unwrap *new-filedata*))
  "int main() {
  int x = 5;
  return x;
}
"))
