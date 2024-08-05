; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")
(include-book "../split-fn-proofs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *filepath-split-fn*
  (filepath "file.SPLIT-FN.c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata1*
  (filedata
   (acl2::string=>nats
    "int foo(int y) {
  int x = 5;
  return x + y;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(split-fn
 *old-transunits1*
 *transunits-split-fn1*
 (c$::ident "foo")
 (c$::ident "bar")
 1
 :proofs t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata2*
  (filedata
   (acl2::string=>nats
     "
int w = 42;

int f(int x) {
  long y = 0, z = 5;
  y = bar(x);
  return x + y + z;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: the name of the theorem should include the transunit const name to
;; avoid name conflicts.
(split-fn
 *old-transunits2*
 *transunits-split-fn2*
 (c$::ident "f")
 (c$::ident "baz")
 1
 :proofs t)
