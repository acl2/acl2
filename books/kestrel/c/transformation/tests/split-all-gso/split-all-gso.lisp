; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

(include-book "../../split-all-gso")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Successes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test1.c")
                   :const *old*)

  (split-all-gso *old* *new*)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test1.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct myStruct_0 { _Bool bar; unsigned long int baz; };
struct myStruct_0_0 { unsigned long int baz; };
struct myStruct_0_1 { _Bool bar; };
struct myStruct_1 { int foo; };
static struct myStruct_0_0 my_0_0;
static struct myStruct_0_1 my_0_1;
static struct myStruct_1 my_1;
int main(void) {
  return my_1.foo + (-my_0_1.bar);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("test2.c")
                   :const *old*)

  (split-all-gso *old* *new*)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/test2.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct myStruct_0 { _Bool bar; unsigned long int baz; };
struct myStruct_0_0 { unsigned long int baz; };
struct myStruct_0_1 { _Bool bar; };
struct myStruct_1 { int foo; };
static struct myStruct_0_0 my_0_0 = {.baz = 42};
static struct myStruct_0_1 my_0_1 = {.bar = 0};
static struct myStruct_1 my_1 = {.foo = 0};
int main(void) {
  int x = my_1.foo + (-my_0_0.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test an ensemble

(acl2::must-succeed*
  (c$::input-files :files '("static-struct1.c"
                           "static-struct2.c"
                           "extern-struct.c")
                   :const *old*)

  (split-all-gso *old* *new*)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/static-struct1.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct myStruct_0 { _Bool bar; unsigned long int baz; };
struct myStruct_0_0 { unsigned long int baz; };
struct myStruct_0_1 { _Bool bar; };
struct myStruct_1 { int foo; };
static struct myStruct_0_0 my_0_0 = {.baz = 42};
static struct myStruct_0_1 my_0_1 = {.bar = 0};
static struct myStruct_1 my_1 = {.foo = 0};
int main(void) {
  int x = my_1.foo + (-my_0_0.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")
  (assert-file-contents
    :file "new/static-struct2.c"
    :content "struct myStruct { int a; int b; };
struct myStruct_2 { int b; };
struct myStruct_3 { int a; };
static struct myStruct_2 my_0 = {.b = 0, };
static struct myStruct_3 my_2 = {.a = 0, };
struct S { int x; };
struct S_0;
struct S_1 { int x; };
struct S_0 s_0;
struct S_1 s_1;
int foo(void) {
  int x = my_2.a + (-my_0.b);
  struct myStruct my;
  if (s_1.x) {
    return my.a + (-my.b);
  }
  return 0;
}
")
  (assert-file-contents
    :file "new/extern-struct.c"
    :content "struct S { unsigned int x; unsigned int y; };
struct S_0 { unsigned int y; };
struct S_1 { unsigned int x; };
struct S_0 s_0;
struct S_1 s_1 = {.x = 0};
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test typedefs

(acl2::must-succeed*
  (c$::input-files :files '("typedef1.c")
                   :const *old*)

  (split-all-gso *old*
                 *new*)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/typedef1.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct myStruct_0 { _Bool bar; unsigned long int baz; };
struct myStruct_0_0 { unsigned long int baz; };
struct myStruct_0_1 { _Bool bar; };
struct myStruct_1 { int foo; };
typedef struct myStruct myStruct_t;
static struct myStruct_0_0 my_0_0;
static struct myStruct_0_1 my_0_1;
static struct myStruct_1 my_1;
int main(void) {
  return my_1.foo + (-my_0_0.baz);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files '("typedef2.c")
                   :const *old*)

  (split-all-gso *old*
                 *new*)

  (c$::output-files :const *new*
                    :path "new")

  (assert-file-contents
    :file "new/typedef2.c"
    :content "typedef struct myStruct { int foo; _Bool bar; unsigned long int baz; } myStruct_t;
struct myStruct_0 { _Bool bar; unsigned long int baz; };
struct myStruct_0_0 { unsigned long int baz; };
struct myStruct_0_1 { _Bool bar; };
struct myStruct_1 { int foo; };
static struct myStruct_0_0 my_0_0;
static struct myStruct_0_1 my_0_1;
static struct myStruct_1 my_1;
int main(void) {
  return my_1.foo + (-my_0_0.baz);
}
")

  :with-output-off nil)
