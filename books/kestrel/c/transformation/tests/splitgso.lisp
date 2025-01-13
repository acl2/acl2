; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../splitgso")

(include-book "../../syntax/parser")
(include-book "../../syntax/printer")
(include-book "../../syntax/validator")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filepath*
  (filepath "file.c"))

(defconst *filepath-splitgso*
  (filepath "file.SPLITGSO.c"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata1*
  (filedata
   (acl2::string=>nats
     "struct myStruct {
  int foo;
  string bar;
  unsigned long int baz;
};

static struct myStruct my;

int main(void) {
  return my.foo + (-my.bar);
}
")))

(defconst *old-fileset1*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata1*
                 nil)))

(defconst *old-transunits1*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset1* nil))
       ((when erp)
        (cw "~@0" erp))
       ((mv erp transunits)
        (c$::valid-transunit-ensemble transunits t (c$::ienv-default)))
       ((when erp)
        (cw "~@0" erp)))
    transunits))

(splitgso *old-transunits1*
          *new-transunits1*
          :object-name "my"
          :new-object1 "my1"
          :new-object2 "my2"
          :new-type1 "s1"
          :new-type2 "s2"
          :split-members ("bar"))

(defconst *fileset-splitgso1*
  (c$::print-fileset *new-transunits1* (c$::default-priopt)))

(defconst *filedata-splitgso1*
  (omap::lookup *filepath-splitgso*
                (fileset->unwrap *fileset-splitgso1*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-splitgso1*))
  "struct myStruct { int foo; string bar; unsigned long int baz; };
struct s1 { int foo; unsigned long int baz; };
struct s2 { string bar; };
static struct s1 my1;
static struct s2 my2;
int main(void) {
  return my1.foo + (-my2.bar);
}
"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *old-filedata2*
  (filedata
   (acl2::string=>nats
     "struct myStruct {
  int foo;
  string bar;
  unsigned long int baz;
};

static struct myStruct my;

int main(void) {
  int x = my.foo + (-my.bar);
  struct myStruct my;
  return my.foo + (-my.bar);
}
")))

(defconst *old-fileset2*
  (fileset
   (omap::update *old-filepath*
                 *old-filedata2*
                 nil)))

(defconst *old-transunits2*
  (b* (((mv erp transunits) (c$::parse-fileset *old-fileset2* nil))
       ((when erp)
        (cw "~@0" erp))
       ((mv erp transunits)
        (c$::valid-transunit-ensemble transunits t (c$::ienv-default)))
       ((when erp)
        (cw "~@0" erp)))
    transunits))

(splitgso *old-transunits2*
          *new-transunits2*
          :object-name "my"
          :new-object1 "my1"
          :new-object2 "my2"
          :new-type1 "s1"
          :new-type2 "s2"
          :split-members ("bar"))

(defconst *fileset-splitgso2*
  (c$::print-fileset *new-transunits2* (c$::default-priopt)))

(defconst *filedata-splitgso2*
  (omap::lookup *filepath-splitgso*
                (fileset->unwrap *fileset-splitgso2*)))

(assert-event
 (equal
   (acl2::nats=>string
     (filedata->unwrap *filedata-splitgso2*))
  "struct myStruct { int foo; string bar; unsigned long int baz; };
struct s1 { int foo; unsigned long int baz; };
struct s2 { string bar; };
static struct s1 my1;
static struct s2 my2;
int main(void) {
  int x = my1.foo + (-my2.bar);
  struct myStruct my;
  return my.foo + (-my.bar);
}
"))
