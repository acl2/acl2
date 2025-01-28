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

(include-book "../../splitgso")
(include-book "../utilities")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Successes

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   :const *old*)

  (splitgso *old*
            *new*
            :object-name "my"
            :new-object1 "my1"
            :new-object2 "my2"
            :new-type1 "s1"
            :new-type2 "s2"
            :split-members ("baz"))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "test1.SPLITGSO.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct s1 { int foo; _Bool bar; };
struct s2 { unsigned long int baz; };
static struct s1 my1;
static struct s2 my2;
int main(void) {
  return my1.foo + (-my1.bar);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test2.c")
                   :const *old*)

  (splitgso *old*
            *new*
            :object-name "my"
            :new-object1 "my1"
            :new-object2 "my2"
            :new-type1 "s1"
            :new-type2 "s2"
            :split-members ("baz"))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "test2.SPLITGSO.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
struct s1 { int foo; _Bool bar; };
struct s2 { unsigned long int baz; };
static struct s1 my1 = {.foo = 0, .bar = 0};
static struct s2 my2 = {.baz = 42};
int main(void) {
  int x = my1.foo + (-my2.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test an ensemble

(acl2::must-succeed*
  (c$::input-files :files ("static-struct1.c"
                           "static-struct2.c"
                           "extern-struct.c")
                   :const *old*)

  (splitgso *old*
            *new*
            :object-name "s"
            ;; :object-filepath "extern-struct.c"
            :new-object1 "s1"
            :new-object2 "s2"
            :new-type1 "S1"
            :new-type2 "S2"
            :split-members ("x"))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "static-struct1.SPLITGSO.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
static struct myStruct my = {.foo = 0, .bar = 0, .baz = 42};
int main(void) {
  int x = my.foo + (-my.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")
  (assert-file-contents
    :file "static-struct2.SPLITGSO.c"
    :content "struct myStruct { int a; int b; };
static struct myStruct my = {.a = 0, .b = 0, };
struct S { int x; };
struct S1;
struct S2 { int x; };
struct S1 s1;
struct S2 s2;
int foo(void) {
  int x = my.a + (-my.b);
  struct myStruct my;
  if (s2.x) {
    return my.a + (-my.b);
  }
  return 0;
}
")
  (assert-file-contents
    :file "extern-struct.SPLITGSO.c"
    :content "struct S { unsigned int x; unsigned int y; };
struct S1 { unsigned int y; };
struct S2 { unsigned int x; };
struct S1 s1;
struct S2 s2 = {.x = 0};
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Same as above, but with the :object-filepath

(acl2::must-succeed*
  (c$::input-files :files ("static-struct1.c"
                           "static-struct2.c"
                           "extern-struct.c")
                   :const *old*)

  (splitgso *old*
            *new*
            :object-name "s"
            :object-filepath "extern-struct.c"
            :new-object1 "s1"
            :new-object2 "s2"
            :new-type1 "S1"
            :new-type2 "S2"
            :split-members ("x"))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "static-struct1.SPLITGSO.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
static struct myStruct my = {.foo = 0, .bar = 0, .baz = 42};
int main(void) {
  int x = my.foo + (-my.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")
  (assert-file-contents
    :file "static-struct2.SPLITGSO.c"
    :content "struct myStruct { int a; int b; };
static struct myStruct my = {.a = 0, .b = 0, };
struct S { int x; };
struct S1;
struct S2 { int x; };
struct S1 s1;
struct S2 s2;
int foo(void) {
  int x = my.a + (-my.b);
  struct myStruct my;
  if (s2.x) {
    return my.a + (-my.b);
  }
  return 0;
}
")
  (assert-file-contents
    :file "extern-struct.SPLITGSO.c"
    :content "struct S { unsigned int x; unsigned int y; };
struct S1 { unsigned int y; };
struct S2 { unsigned int x; };
struct S1 s1;
struct S2 s2 = {.x = 0};
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("static-struct1.c"
                           "static-struct2.c"
                           "extern-struct.c")
                   :const *old*)

  (splitgso *old*
            *new*
            :object-name "my"
            :object-filepath "static-struct2.c"
            :new-object1 "my1"
            :new-object2 "my2"
            :new-type1 "myStruct1"
            :new-type2 "myStruct2"
            :split-members ("b"))

  (c$::output-files :const *new*)

  (assert-file-contents
    :file "static-struct1.SPLITGSO.c"
    :content "struct myStruct { int foo; _Bool bar; unsigned long int baz; };
static struct myStruct my = {.foo = 0, .bar = 0, .baz = 42};
int main(void) {
  int x = my.foo + (-my.baz);
  struct myStruct my;
  return my.foo + (-my.baz);
}
")
  (assert-file-contents
    :file "static-struct2.SPLITGSO.c"
    :content "struct myStruct { int a; int b; };
struct myStruct1 { int a; };
struct myStruct2 { int b; };
static struct myStruct1 my1 = {.a = 0, };
static struct myStruct2 my2 = {.b = 0, };
struct S { int x; };
extern struct S s;
int foo(void) {
  int x = my1.a + (-my2.b);
  struct myStruct my;
  if (s.x) {
    return my.a + (-my.b);
  }
  return 0;
}
")
  (assert-file-contents
    :file "extern-struct.SPLITGSO.c"
    :content "struct S { unsigned int x; unsigned int y; };
struct S s = {.x = 0};
")

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Failures

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test1.c")
                   ;; Not validating
                   :process :disambiguate
                   :const *old*)

  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("bar")))

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("test3.c")
                   :const *old*)

  ;; Global struct object occurs outside of field access.
  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("baz"))
    :with-output-off nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("weird_initializer.c")
                   :process :validate
                   :const *old*)

  ;; Unsupported initializer
  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("baz"))

    :with-output-off nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("static_assert_struct_declaration.c")
                   :process :validate
                   :const *old*)

  ;; Unsupported static assert struct declaration
  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("baz"))

    :with-output-off nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("simultaneous_struct_fields.c")
                   :process :validate
                   :const *old*)

  ;; Unsupported multiple struct declarators
  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("baz"))

    :with-output-off nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("simultaneous_init_declors.c")
                   :process :validate
                   :const *old*)

  ;; Unsupported simultaneous struct initializer/declarations
  (must-fail
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "s1"
              :new-type2 "s2"
              :split-members ("baz"))

    :with-output-off nil)

  :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::must-succeed*
  (c$::input-files :files ("static-struct1.c"
                           "static-struct2.c"
                           "extern-struct.c")
                   :const *old*)

  ;; (must-fail
    ;; TODO: should this fail? the struct object it finds is static. Should we
    ;;   force :object-filepath?
    (splitgso *old*
              *new*
              :object-name "my"
              :new-object1 "my1"
              :new-object2 "my2"
              :new-type1 "myStruct1"
              :new-type2 "myStruct2"
              :split-members ("b"))

    ;; :with-output-off nil)

  :with-output-off nil)
