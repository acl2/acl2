; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../copy-fn")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *filepath-copy-fn*
  (filepath "file.COPY-FN.c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata1*
  (filedata
   (acl2::string=>nats
    "int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
")))

(defconst *old-fileset1*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata1*
                 nil)))

(defconst *old-transunits1*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset1* nil)))
    (if erp
        (cw "~@0" erp)
      transunits)))

(defconst *transunits-copy-fn1*
  (copy-fn-transunit-ensemble *old-transunits1*
                              (c$::ident "foo")
                              (c$::ident "bar")))

(defconst *fileset-copy-fn1*
  (c$::print-fileset *transunits-copy-fn1* (c$::default-priopt)))

(defconst *filedata-copy-fn1*
  (omap::lookup *filepath-copy-fn*
                (fileset->unwrap *fileset-copy-fn1*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-copy-fn1*))
  "int foo(int y, int z) {
  int x = 5;
  return x + y - z;
}
int bar(int y, int z) {
  int x = 5;
  return x + y - z;
}
"))
