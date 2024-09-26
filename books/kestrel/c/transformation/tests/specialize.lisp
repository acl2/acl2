; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../specialize")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *filepath-specialize*
  (filepath "file.SPECIALIZE.c"))

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

(defconst *transunits-specialize1*
  (b* ((const
         (expr-const
           (c$::const-int
             (c$::make-iconst :core (c$::dec/oct/hex-const-dec 1))))))
    (specialize-transunit-ensemble *old-transunits1*
                                   (c$::ident "foo")
                                   (c$::ident "y")
                                   const)))

(defconst *fileset-specialize1*
  (c$::print-fileset *transunits-specialize1* (c$::default-priopt)))

(defconst *filedata-specialize1*
  (omap::lookup *filepath-specialize*
                (fileset->unwrap *fileset-specialize1*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-specialize1*))
  "int foo(int z) {
  int y = 1;
  int x = 5;
  return x + y - z;
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata2*
  (filedata
   (acl2::string=>nats
    "int foo(int y, int z) {
  int x = 5;
  z++;
  return x + y - z;
}
")))

(defconst *old-fileset2*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata2*
                 nil)))

(defconst *old-transunits2*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset2* nil)))
    (if erp
        (cw "~@0" erp)
      transunits)))

(defconst *transunits-specialize2*
  (b* ((const
         (expr-const
           (c$::const-int
             (c$::make-iconst :core (c$::dec/oct/hex-const-dec 42))))))
    (specialize-transunit-ensemble *old-transunits2*
                                   (c$::ident "foo")
                                   (c$::ident "z")
                                   const)))

(defconst *fileset-specialize2*
  (c$::print-fileset *transunits-specialize2* (c$::default-priopt)))

(defconst *filedata-specialize2*
  (omap::lookup *filepath-specialize*
                (fileset->unwrap *fileset-specialize2*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-specialize2*))
  "int foo(int y) {
  int z = 42;
  int x = 5;
  z++;
  return x + y - z;
}
"))
