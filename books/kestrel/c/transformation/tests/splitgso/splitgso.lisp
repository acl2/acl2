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
                   :process :validate
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
                   :process :validate
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
                   :process :validate
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
