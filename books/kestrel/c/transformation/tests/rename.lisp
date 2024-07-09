; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")


(include-book "../rename")

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


(defconst *transunits-rename*
  (rename-transunit-ensemble *old-transunits*
                             (acons (c$::ident "main") (c$::ident "entry")
                                    (acons (c$::ident "x") (c$::ident "y")
                                           nil))))

(defconst *fileset-rename*
  (c$::print-fileset *transunits-rename*))

(defconst *filepath-rename*
  (filepath "file.RENAME.c"))

(defconst *filedata-rename*
  (omap::lookup *filepath-rename*
                (fileset->unwrap *fileset-rename*)))

(assert-event
 (equal
  (acl2::nats=>string
   (filedata->unwrap *filedata-rename*))
  "int entry() {
  int y = 5;
  return y + 0;
}
"))
