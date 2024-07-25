; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../split-fn")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")

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

(defconst *transunits-split-fn1*
  (b* (((mv er ensemble)
        (split-fn-transunit-ensemble (c$::ident "foo")
                                     (c$::ident "bar")
                                     *old-transunits1*
                                     1)))
    (if er
        (cw "~@0" er)
      ensemble)))

(defconst *fileset-split-fn1*
  (c$::print-fileset *transunits-split-fn1*))

(defconst *filedata-split-fn1*
  (omap::lookup *filepath-split-fn*
                (fileset->unwrap *fileset-split-fn1*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-split-fn1*))
  "int bar(int x, int y) {
  return x + y;
}
int foo(int y) {
  int x = 5;
  return bar(x, y);
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata2*
  (filedata
   (acl2::string=>NATS
    "unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  for (unsigned int i = 0; i < len; i++) {
    total -= arr[i];
  }
  return (unsigned long)total;
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

(defconst *transunits-split-fn2*
  (b* (((mv er ensemble)
        (split-fn-transunit-ensemble (c$::ident "add_and_sub_all")
                                     (c$::ident "sub_all")
                                     *old-transunits2*
                                     2)))
    (if er
        (cw "~@0" er)
      ensemble)))

(defconst *fileset-split-fn2*
  (c$::print-fileset *transunits-split-fn2*))

(defconst *filedata-split-fn2*
  (omap::lookup *filepath-split-fn*
                (fileset->unwrap *fileset-split-fn2*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-split-fn2*))
  "unsigned long sub_all(long arr[], unsigned int len, long total) {
  for (unsigned int i = 0; i < len; i++) {
    total -= arr[i];
  }
  return (unsigned long) total;
}
unsigned long add_and_sub_all(long arr[], unsigned int len) {
  long total = 0l;
  for (unsigned int i = 0; i < len; i++) {
    total += arr[i];
  }
  return sub_all(arr, len, total);
}
"))
