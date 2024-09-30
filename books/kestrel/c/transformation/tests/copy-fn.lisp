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

(include-book "../../syntax/disambiguator")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata2*
  (filedata
   (acl2::string=>nats
    "int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x-1) + fibonacci(x-2);
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

(defconst *transunits-copy-fn2*
  (copy-fn-transunit-ensemble *old-transunits2*
                              (c$::ident "fibonacci")
                              (c$::ident "fib")))

(defconst *fileset-copy-fn2*
  (c$::print-fileset *transunits-copy-fn2* (c$::default-priopt)))

(defconst *filedata-copy-fn2*
  (omap::lookup *filepath-copy-fn*
                (fileset->unwrap *fileset-copy-fn2*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-copy-fn2*))
  "int fibonacci(int x) {
  if (x <= 1) {
    return x;
  }
  return fibonacci(x - 1) + fibonacci(x - 2);
}
int fib(int x) {
  if (x <= 1) {
    return x;
  }
  return fib(x - 1) + fib(x - 2);
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This example shows the nuance of looking for direct recursive calls. Here,
;; the function foo is within a generic selection, which itself is (needlessly)
;; parenthesized. There is also a statement expression which uses the name of
;; the function as the name of a variable of a different type, which clearly
;; should not be renamed.
(defconst *old-filedata3*
  (filedata
   (acl2::string=>nats
    "int foo(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: foo))(({ int foo = x-1; foo; }));
}
")))

(defconst *old-fileset3*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata3*
                 nil)))

(defconst *old-transunits3*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset3* t))
       ((when erp)
        (cw "~@0" erp))
       ((mv erp transunits) (c$::dimb-transunit-ensemble transunits t)))
    (if erp
        (cw "~@0" erp)
      transunits)))

(defconst *transunits-copy-fn3*
  (copy-fn-transunit-ensemble *old-transunits3*
                              (c$::ident "foo")
                              (c$::ident "bar")))

(defconst *fileset-copy-fn3*
  (c$::print-fileset *transunits-copy-fn3* (c$::default-priopt)))

(defconst *filedata-copy-fn3*
  (omap::lookup *filepath-copy-fn*
                (fileset->unwrap *fileset-copy-fn3*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-copy-fn3*))
  "int foo(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: foo))(({
    int foo = x - 1;
    foo;
  }));
}
int bar(int x) {
  if (x == 0) {
    return x;
  }
  return (_Generic((x), default: bar))(({
    int foo = x - 1;
    foo;
  }));
}
"))
